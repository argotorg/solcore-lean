import Solcore.Frontend.RustHull.CodeImage
import Solcore.Core.Machine
import Solcore.Frontend.RustHull.ContractCodeTheorems
import Solcore.Frontend.RustHull.Semantics.Layers
import Solcore.Frontend.RustHull.Effects
import Solcore.Abi.Keccak256
import Solcore.Frontend.RustHull.Contract
import Solcore.Frontend.RustHull.Internal.Creation
import Solcore.Frontend.RustHull.ContractCallTheorems
import Solcore.Frontend.RustHull.Internal.CallLayout
import Solcore.Frontend.RustHull.LinkedContract

/-!
# Hull creation tests

CREATE and CREATE2, code images, object linking and linked contracts.
-/

section
-- leanmerge: from Solcore.Test.RustHullCodeImage
set_option autoImplicit false
namespace Tests.RustHullCodeImage
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def success {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def emptyCode : CodeBlock := {stmts := [], functions := []}

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def scalar (value : Nat) : Value := .word (Word.ofNatModulo value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def images : List CodeImage.Image := [
  {path := ["Root"], bytes := bytes [1, 2, 3, 4, 5, 6, 7],
    embeds := [{name := "A", offset := 2, size := 3}, {name := "B", offset := 5, size := 2}]},
  {path := ["Root", "A"], bytes := bytes [3, 4, 5], embeds := [{name := "Leaf", offset := 2, size := 1}]},
  {path := ["Root", "A", "Leaf"], bytes := bytes [5]},
  {path := ["Root", "B"], bytes := bytes [6, 7]}]
private def objects : List Object := [
  .object "Root" emptyCode [
    .object "A" emptyCode [.object "Leaf" emptyCode [] none] none,
    .object "B" emptyCode [] none] none]

private def memory (body : Expr) : Expr :=
  .letE (.newCell WordMapping.type WordMapping.empty)
    (.letE (.newCell .word (word 0)) body)

private def sequence (result : Ty) (action next : Expr) : Expr :=
  LanguageResult.bind result action (next.weakenAt 0)

private def expect (label : String) (type : Ty) (body : Expr) (expected : Value) : IO Unit := do
  let program : Program := {
    resultType := LanguageResult.resultType type
    body
    dataDefinitions := Memory.definitions
  }
  require program.check s!"{label}: ill-typed Core"
  match program.run 3000000 with
  | .done actual => require (actual == .inRight .word expected) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def jsonEnvelope (entries : String) : String :=
  "{\"schema\":\"solcore-rs.code-images.v1\",\"upstreamCommit\":\"" ++ upstreamCommit ++
  "\",\"backend\":{\"name\":\"sonatina\",\"revision\":\"" ++ CodeImage.backendRevision ++
  "\",\"optimization\":\"O0\"},\"images\":" ++ entries ++ "}"

def run : IO Unit := do
  let _ ← success (CodeImage.validate objects images)
  let root ← success (CodeImage.select images ["Root"])
  let a ← success (CodeImage.select images ["Root", "A"])
  require ((← success (CodeImage.resolve root "Root")) == ⟨0, 7⟩) "current section extent"
  require ((← success (CodeImage.resolve root "A")) == ⟨2, 3⟩) "direct embed extent"
  require ((← success (CodeImage.resolve a "Leaf")) == ⟨2, 1⟩) "nested relative extent"
  require (CodeImage.resolve root "Leaf" |> rejected) "nested symbol leaked into parent namespace"
  require (CodeImage.select images ["A"] |> rejected) "suffix path accepted as full path"
  require (CodeImage.validate objects images.tail |> rejected) "missing image accepted"
  require (CodeImage.validate objects (root :: images) |> rejected) "duplicate image accepted"
  require (CodeImage.validate objects ({root with bytes := bytes [1, 2, 9, 4, 5, 6, 7]} :: images.tail) |> rejected)
    "mismatched child bytes accepted"
  let badExtent := {root with embeds := [{name := "A", offset := 6, size := 3},
      {name := "B", offset := 5, size := 2}]}
  require (CodeImage.validate objects (badExtent :: images.tail) |> rejected) "out-of-range embed accepted"
  let overlappingObjects := [.object "Root" emptyCode [.object "A" emptyCode [] none, .object "B" emptyCode [] none] none]
  let overlapping : List CodeImage.Image := [
    {path := ["Root"], bytes := bytes [1, 2, 3],
      embeds := [{name := "A", offset := 0, size := 2}, {name := "B", offset := 1, size := 2}]},
    {path := ["Root", "A"], bytes := bytes [1, 2]},
    {path := ["Root", "B"], bytes := bytes [2, 3]}]
  require (CodeImage.validate overlappingObjects overlapping |> rejected) "overlapping child images accepted"
  let execution ← success (CodeImage.executionBytes root (bytes [0xaa, 0xbb]))
  require ((← success (CodeImage.resolve root "Root")).size = 7) "constructor arguments changed datasize"
  expect "codesize includes constructor input" .word (CodeImage.codeSize execution) (scalar 9)
  expect "copy constructor suffix" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 7) (word 2))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0xaabb * 256 ^ 30))
  expect "copy embedded runtime" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 2) (word 3))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0x030405 * 256 ^ 29))
  expect "codecopy zero pads" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0) (word 0) (word 8) (word 4))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar (0xbb * 256 ^ 31))
  expect "codecopy source does not wrap" .word
    (memory (sequence .word (CodeImage.copy execution (.var 1) (.var 0)
      (word 0) (word (wordModulus - 1)) (word 2))
      (Memory.mload (.var 1) (.var 0) (word 0)))) (scalar 0)
  let json := jsonEnvelope "[{\"path\":[\"Root\"],\"bytes\":\"0x0102ff\",\"embeds\":[]}]"
  let decoded ← success (CodeImage.decode json)
  require (decoded == [{path := ["Root"], bytes := bytes [1, 2, 255]}]) "code image decode"
  require ((← success (CodeImage.decode (json.replace "O0" "O2"))) == decoded)
    "pinned Sonatina O2 code image rejected"
  for malformed in [json.replace "0x0102ff" "0x1", json.replace "0x0102ff" "0xFF",
      json.replace "O0" "O1", json.replace "O0" "O3", json.replace "O0" "o2",
      json.replace "O0" "", json.replace "sonatina" "yul",
      json.replace upstreamCommit "wrong", json.replace CodeImage.backendRevision "wrong",
      json.replace "\"embeds\":[]" "\"embeds\":[],\"extra\":0"] do
    require (CodeImage.decode malformed |> rejected) "malformed artifact accepted"
  for malformed in [String.ofList (List.replicate 17 '['),
      json.replace "\"embeds\":[]" "\"embeds\":1e999999999",
      json.replace "\"embeds\":[]" "\"embeds\":12345678901"] do
    require (CodeImage.decode malformed |> rejected) "parser resource guard ignored"
  require (CodeImage.decode json 10 |> rejected) "artifact input byte limit ignored"

end Tests.RustHullCodeImage
end

section
-- leanmerge: from Solcore.Test.RustHullCodeImageCorrespondence
/-! Linked code images reach source copying and public execution. Empty known
images zero-fill, while unavailable root images remain faults even when another
object is present in the code catalog. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCodeImageCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where | codeCopy | dataCopy | size | empty | unknown | overflow | zero | unknownSize | emptySize
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def maximum := "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩
def codeBytes : List UInt8 := [171, 205]
def image : Scenario → Option (List UInt8)
  | .unknown | .unknownSize => none
  | .empty | .emptySize => some []
  | _ => some codeBytes

def library : AccountRuntime.CodeDefinition := {
  program := {entryPoints := [], functions := [], objects := [.object "Library" {stmts := [], functions := []} []]}
  path := ["Library"]
  bytes := [153]
}
def catalog : Scenario → List AccountRuntime.CodeDefinition
  | .size | .unknown | .unknownSize => [library]
  | _ => []
theorem enabled (scenario : Scenario) : ((image scenario).isSome || !(catalog scenario).isEmpty) = true := by cases scenario <;> rfl

def copying : Scenario → Bool | .size | .unknownSize | .emptySize => false | _ => true
def operation : Scenario → CodeImageSemantics.Operation | .dataCopy => .dataCopy | _ => .codeCopy
def destination : Scenario → Core.Word
  | .overflow | .zero => Core.Word.maximum
  | .codeCopy => w 7
  | _ => w 31
def sourceOffset : Scenario → Core.Word
  | .zero => Core.Word.maximum
  | .codeCopy | .overflow => w 0
  | _ => w 1
def count : Scenario → Core.Word | .zero => w 0 | .codeCopy => w 2 | .overflow => w 1 | _ => w 3
def copyCall (scenario : Scenario) : Expr := match scenario with
  | .codeCopy => call .unit "codecopy" [word "7", word "0", word "2"]
  | .dataCopy => call .unit "datacopy" [word "31", word "1", word "3"]
  | .overflow => call .unit "codecopy" [word maximum, word "0", word "1"]
  | .zero => call .unit "codecopy" [word maximum, word maximum, word "0"]
  | _ => call .unit "codecopy" [word "31", word "1", word "3"]
def seed : Expr := call .unit "mstore8" [word "3", word "17"]
def sizeCall : Expr := call .word "codesize" []
def inspect (scenario : Scenario) : Expr :=
  if copying scenario then copyCall scenario else call .unit "mstore" [word "192", sizeCall]
def returned (scenario : Scenario) : Expr := match scenario with
  | .codeCopy => call .unit "return" [word "7", word "2"]
  | .size | .unknownSize | .emptySize => call .unit "return" [word "192", word "32"]
  | .zero => call .unit "return" [word "3", word "1"]
  | _ => call .unit "return" [word "31", word "3"]
def code (scenario : Scenario) : CodeBlock := {stmts := [expression seed, expression (inspect scenario), expression (returned scenario)], functions := []}
def program (scenario : Scenario) : Program := {entryPoints := [], functions := [], objects := [.object "Image" (code scenario) []]}
def context : Contract.Context := {}
def initial (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeCodeEffectsSemantics.State :=
  ⟨[], ContractCodeCorrespondence.contextInitialState (image scenario) object (Contract.normalizeContext context)⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 3) (w 17)).2
def memoryState (object : Contract.CompiledObject) (scenario : Scenario) (memory : MemorySemantics.State) : Semantics.State RuntimeCodeEffectsSemantics.State :=
  ⟨[], RuntimeAccountEffectsSemantics.withMemory (initial object scenario).external memory⟩
def copyWords (scenario : Scenario) : MemorySemantics.Entries :=
  if scenario = .codeCopy then
    MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 7) (w 171)) (w 8) (w 205)
  else if scenario = .dataCopy then
    MemorySemantics.writeByte (MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 31) (w 205)) (w 32) (w 0)) (w 33) (w 0)
  else if scenario = .empty then
    MemorySemantics.writeByte (MemorySemantics.writeByte (MemorySemantics.writeByte seeded.words (w 31) (w 0)) (w 32) (w 0)) (w 33) (w 0)
  else seeded.words
def copyMemory (scenario : Scenario) : MemorySemantics.State :=
  ⟨copyWords scenario, if scenario = .dataCopy ∨ scenario = .empty then w 64 else w 32⟩
def fails : Scenario → Bool | .unknown | .unknownSize | .overflow => true | _ => false
def failureReason : Scenario → Core.Word | .overflow => w 6 | _ => w 15
def inspectResult (scenario : Scenario) : Semantics.Result Semantics.Value :=
  if fails scenario then .fault (.language (failureReason scenario)) else .value .unit

theorem copy_source (scenario : Scenario) (isCopy : copying scenario = true) :
    CodeImageSemantics.Execute (image scenario) (destination scenario) (sourceOffset scenario) (count scenario) seeded
      (if scenario = .unknown ∨ scenario = .unknownSize then CodeImageSemantics.unavailable
       else if scenario = .overflow then MemorySemantics.overflow else .value .unit)
      (copyMemory scenario) := by
  cases scenario
  case unknown => exact .unknown rfl
  case unknownSize => exact .unknown rfl
  case overflow => exact .copied rfl (.overflow (by decide +kernel))
  case zero => exact .copied rfl (.done (by decide +kernel) (.empty _ _ _ _))
  case codeCopy =>
    apply CodeImageSemantics.Execute.copied rfl
    apply MemoryCopySemantics.From.done (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _
  case dataCopy =>
    apply CodeImageSemantics.Execute.copied rfl
    apply MemoryCopySemantics.From.done (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _
  case empty =>
    apply CodeImageSemantics.Execute.copied rfl
    apply MemoryCopySemantics.From.done (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    apply MemoryCopySemantics.Copy.step (by decide +kernel)
    exact .empty _ _ _ _
  case size => contradiction
  case emptySize => contradiction

def observedWord (scenario : Scenario) : Core.Word := w ((image scenario).getD []).length
def inspectedMemory (scenario : Scenario) : MemorySemantics.State :=
  if copying scenario then copyMemory scenario else
  if fails scenario then seeded else (MemorySemantics.mstore seeded (w 192) (observedWord scenario)).2
def returnOffset : Scenario → Core.Word
  | .codeCopy => w 7 | .size | .unknownSize | .emptySize => w 192 | .zero => w 3 | _ => w 31
def returnLength : Scenario → Core.Word
  | .codeCopy => w 2 | .size | .unknownSize | .emptySize => w 32 | .zero => w 1 | _ => w 3
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : Semantics.State RuntimeCodeEffectsSemantics.State :=
  if fails scenario then memoryState object scenario seeded else
    let state := (memoryState object scenario (inspectedMemory scenario)).external
    let memory := state.runtime.runtime.runtime
    let completed := RuntimeFullEffectsSemantics.withRuntime state.runtime
      (TerminationSemantics.terminate memory 1 (returnOffset scenario) (returnLength scenario)).2
    ⟨[], {state with runtime := completed}⟩
def reason (scenario : Scenario) : Core.Word := if fails scenario then failureReason scenario else Core.Word.maximum
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario)) [] seed
      (initial object scenario) (.value .unit) (memoryState object scenario seeded) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "3") rfl) (.cons (.word (text := "17") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))

private theorem copy_expression (object : Contract.CompiledObject) (scenario : Scenario) (isCopy : copying scenario = true) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario)) [] (copyCall scenario)
      (memoryState object scenario seeded) (inspectResult scenario) (memoryState object scenario (copyMemory scenario)) := by
  have copied := copy_source scenario isCopy
  cases scenario
  case size => contradiction
  case unknownSize => contradiction
  case emptySize => contradiction
  case codeCopy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy .codeCopy copied))
  case overflow =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy .codeCopy copied))
  case zero =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := maximum) rfl) (.cons (.word (text := maximum) rfl) (.cons (.word (text := "0") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy .codeCopy copied))
  case dataCopy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "31") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy .dataCopy copied))
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "31") rfl) (.cons (.word (text := "1") rfl) (.cons (.word (text := "3") rfl) .nil))
    · exact .external (by rfl) rfl (.copy (.copy .codeCopy copied))

private theorem size_source (object : Contract.CompiledObject) (scenario : Scenario) (isSize : copying scenario = false) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario)) [] sizeCall
      (memoryState object scenario seeded)
      (if fails scenario then .fault (.language (failureReason scenario)) else .value (.word (observedWord scenario)))
      (memoryState object scenario seeded) := by
  cases scenario <;> (try contradiction)
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .nil
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))

private theorem inspect_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario)) [] (inspect scenario)
      (memoryState object scenario seeded) (inspectResult scenario) (memoryState object scenario (inspectedMemory scenario)) := by
  cases isCopy : copying scenario with
  | true =>
      simpa only [inspect, inspectedMemory, isCopy, ↓reduceIte] using copy_expression object scenario isCopy
  | false =>
      have observed := size_source object scenario isCopy
      cases failed : fails scenario with
      | true =>
          simp only [inspect, inspectedMemory, inspectResult, isCopy, failed, Bool.false_eq_true, ↓reduceIte]
          simp only [failed, ↓reduceIte] at observed
          apply Semantics.EvalExpr.callFault rfl
          exact .cons (.word (text := "192") rfl) (.fault observed)
      | false =>
          simp only [inspect, inspectedMemory, inspectResult, isCopy, failed, Bool.false_eq_true, ↓reduceIte]
          simp only [failed, Bool.false_eq_true, ↓reduceIte] at observed
          apply Semantics.EvalExpr.call rfl
          · exact .cons (.word (text := "192") rfl) (.cons observed .nil)
          · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) (successful : fails scenario = false) :
    Semantics.EvalExpr [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario)) [] (returned scenario)
      (memoryState object scenario (inspectedMemory scenario)) (result scenario) (finalState object scenario) := by
  simp only [result, reason, finalState, successful, Bool.false_eq_true, ↓reduceIte]
  cases scenario
  case unknown => contradiction
  case unknownSize => contradiction
  case overflow => contradiction
  case codeCopy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "7") rfl) (.cons (.word (text := "2") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))
  case zero =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "3") rfl) (.cons (.word (text := "1") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))
  case dataCopy =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "31") rfl) (.cons (.word (text := "3") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))
  case empty =>
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "31") rfl) (.cons (.word (text := "3") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "192") rfl) (.cons (.word (text := "32") rfl) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction [AccountRuntime.frameFunction (code scenario)] (RuntimeCodeEffectsSemantics.effects (image scenario))
      (AccountRuntime.frameFunction (code scenario)) [] (initial object scenario) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl (seed_source object scenario))
  have inspected := inspect_source object scenario
  cases successful : fails scenario with
  | true =>
      have unchanged : inspectedMemory scenario = seeded := by cases scenario <;> first | contradiction | rfl
      simp only [inspectResult, successful, unchanged, ↓reduceIte] at inspected
      simp only [reason, finalState, successful, ↓reduceIte]
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl inspected)
        (by intro impossible; cases impossible)
  | false =>
      simp only [inspectResult, successful, Bool.false_eq_true, ↓reduceIte] at inspected
      apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible) (.expression rfl inspected)
      exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario successful))
        (by intro impossible; cases impossible)

private theorem copy_eligible (scenario : Scenario) :
    ExecutableExpression ContractCodeCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] (copyCall scenario) := by
  cases scenario
  all_goals
    first
    | apply ExecutableExpression.external (Or.inr (Or.inr ⟨.codeCopy, rfl⟩)) (by rfl)
    | apply ExecutableExpression.external (Or.inr (Or.inr ⟨.dataCopy, rfl⟩)) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact .word _ _ _

theorem eligible (scenario : Scenario) :
    ExecutableProgram ContractCodeCorrespondence.supported [AccountRuntime.frameFunction (code scenario)] := by
  intro function member statement statementMember
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore8")
      (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store8, rfl⟩)))))))) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .word _ _ _
  · cases isCopy : copying scenario with
    | true => simpa only [inspect, isCopy, ↓reduceIte] using copy_eligible scenario
    | false =>
      simp only [inspect, isCopy, Bool.false_eq_true, ↓reduceIte]
      apply ExecutableExpression.external (name := "mstore")
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨.store, rfl⟩)))))))) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .word _ _ _
      · exact .external (Or.inr (Or.inl rfl)) (by rfl) (by intro _ member; cases member) _ _
  · cases scenario
    all_goals
      apply ExecutableExpression.external (name := "return")
        (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨.returned, rfl⟩))))) (by rfl)
      intro argument member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact .word _ _ _

theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Image"] 64 (image scenario) (catalog scenario) = .ok object) :
    ∃ value, ContractCodeCorrespondence.PublicMessageRel context (result scenario) (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit) additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) :=
  ContractCodeCorrespondence.compileObject_resumes_exact (code := code scenario) (by rfl)
    accepted (enabled scenario) (eligible scenario) context rfl (source object scenario)

private def wordBytes (value : Core.Word) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (Core.Word.byteAt (w index) value).val
private def expectedBytes (scenario : Scenario) : List UInt8 := match scenario with
  | .codeCopy => [171, 205]
  | .dataCopy => [205, 0, 0]
  | .empty => [0, 0, 0]
  | .zero => [17]
  | _ => wordBytes (observedWord scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Image"] 64 (image scenario) (catalog scenario) with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"code-image correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"code-image correspondence: zero fuel completed: {reprStr outcome}")
  let checkpoint ← match (Contract.resumeWithReceipt checkpoint 19).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"code-image correspondence: short resume completed: {reprStr outcome}")
  let receipt := Contract.resumeWithReceipt checkpoint 10000000
  if fails scenario then
    match receipt.outcome with
    | .languageFailure (.word reason) =>
        unless reason == failureReason scenario && receipt.world.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError "code-image correspondence: failure reason or receipt differs")
    | outcome => throw (IO.userError s!"code-image correspondence: expected failure, got {reprStr outcome}")
  else
    match receipt.outcome with
    | .returned bytes storage =>
        unless bytes == expectedBytes scenario && storage.isEmpty && receipt.logs.isEmpty do
          throw (IO.userError s!"code-image correspondence: returned observation differs in {reprStr scenario}")
    | outcome => throw (IO.userError s!"code-image correspondence: expected return, got {reprStr outcome}")
  match Core.runStateful 10000000 (Core.State.initial prepared.expression) with
  | .done (.pair _ (.pair exit (.pair offset (.pair size (.pair memory (.pair _ (.pair _ (.pair _ (.pair balances _))))))))) _ =>
      let expected := (finalState object scenario).external
      let runtime := expected.runtime.runtime.runtime
      unless memory == Core.WordMapping.encode runtime.memory.words && balances == Core.WordMapping.encode expected.balances &&
          exit == .word runtime.storage.exit && offset == .word runtime.storage.returnOffset && size == .word runtime.storage.returnSize do
        throw (IO.userError s!"code-image correspondence: public snapshot differs in {reprStr scenario}")
      unless MemoryCopySemantics.readByte runtime.memory.words (w 3) == w 17 do
        throw (IO.userError "code-image correspondence: copying changed memory outside the destination")
  | outcome => throw (IO.userError s!"code-image correspondence: Core failed: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.codeCopy, .dataCopy, .size, .empty, .unknown, .overflow, .zero, .unknownSize, .emptySize] do
    check scenario

end Tests.RustHullCodeImageCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCreation
set_option autoImplicit false
namespace Tests.RustHullCreation
open Solcore.Core
open Solcore.Frontend.RustHull hiding Expr Ty Program

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def number (value : Nat) : Expr := .word (word value)
private def scalar (value : Nat) : Value := .word (word value)
private def ok (value : Nat) : Value := .inRight .word (scalar value)
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat

private def execute (label : String) (compiled : Program) (expected : Value) : IO Store := do
  require compiled.check s!"{label}: ill-typed creation Core"
  match compiled.runStateful 10000000 with
  | .done value store =>
      require (value == expected) s!"{label}: {reprStr value}"
      pure store
  | other => throw (IO.userError s!"{label}: {reprStr other}")

private def addressProgram (creator nonce : Nat) : Program := {
  resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
  body := Creation.createAddress (number creator) (number nonce)}

private def address2Program (input : List UInt8) (creator salt offset length : Nat) : Program := {
  resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
  body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
    (.letE (.newCell .word (number 0))
      (Creation.create2Address (.var 1) (.var 0) (number creator) (number salt) (number offset) (number length)))}

private def digest (input : List UInt8) : Nat :=
  (Solcore.Abi.V1.Keccak256.hash input.toByteArray).data.foldl
    (fun value byte => value * 256 + byte.toNat) 0
private def wordBytes (length value : Nat) : List UInt8 :=
  (List.range length).map fun index => UInt8.ofNat (value / 256 ^ (length - 1 - index) % 256)
private def expectedAddress2 (creator salt : Nat) (input : List UInt8) : Nat :=
  digest (bytes [255] ++ wordBytes 20 creator ++ wordBytes 32 salt ++ wordBytes 32 (digest input)) % 2 ^ 160

private def resumeChunks : Nat → State → IO StatefulRunResult
  | 0, _ => throw (IO.userError "creation resume budget exhausted")
  | attempts + 1, state => match runStateful 5000 state with
      | .outOfFuel state => resumeChunks attempts state
      | result => pure result

private def addressTests : IO Unit := do
  -- Independent cast compute-address and RLP/Keccak vectors are recorded in
  -- Tests/Fixtures/EvmAccounts/address-vectors.json.
  let creator := 0xdeadbeef * 2 ^ 128
  for (nonce, expected) in [
      (0, 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea),
      (1, 0x054dd934335ea61232ae4c051f8bf20e540f8291),
      (127, 0x7feb088e1893d4a1087288d386c07252abb3c02e),
      (128, 0x2297787b25b800d655071345a1d3a7951404b50c),
      (255, 0xc8d17a8bdb6001525f8594e3ca4413d4bd644605),
      (256, 0xa0ddf5980551b5ec83721bcf168785ac3cedb183),
      (2 ^ 64 - 1, 0x66e93872e94cc56d1da3bb63f81dabd9c1d6c125)] do
    let _ ← execute s!"CREATE nonce {nonce}" (addressProgram creator nonce) (ok expected)
  let _ ← execute "CREATE ignores creator high bits" (addressProgram (creator + 2 ^ 200) 0)
    (ok 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea)
  for (address, salt, input, expected) in [
      (0, 0, bytes [0], 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38),
      (creator, 0, bytes [0], 0xb928f69bb1d91cd65274e3c79d8986362984fda3),
      (creator, 22207167547627365064083290255604625247830016, bytes [0],
        0xf2a2934e8506d97a2cee99962533f9729676ae24),
      (0xdeadbeef, 0xcafebabe, bytes [0xde, 0xad, 0xbe, 0xef],
        0x60f3f640a8508fc6a86d45df051962668e1e8ac7)] do
    let store ← execute "CREATE2 independent vector"
      (address2Program input address salt 0 input.length) (ok expected)
    require (store[0]? == some (WordMapping.encode (Memory.packBytes input)))
      "CREATE2 derivation changed caller memory"
    require (store[1]? == some (scalar 32)) "CREATE2 input range did not expand memory"
  let input := (List.range 147).map fun index => UInt8.ofNat (index * 19 + 5)
  let expected := expectedAddress2 creator (wordModulus - 1) ((input.drop 7).take 137)
  let compiled := address2Program input (creator + 2 ^ 200) (wordModulus - 1) 7 137
  let store ← execute "CREATE2 unaligned multi-block init" compiled (ok expected)
  require (store[0]? == some (WordMapping.encode (Memory.packBytes input)) &&
    store[1]? == some (scalar 160)) "CREATE2 scratch memory escaped into caller memory"
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint => match ← resumeChunks 1000 checkpoint with
      | .done value _ => require (value == ok expected) "CREATE2 address changed across resumes"
      | other => throw (IO.userError s!"CREATE2 resume: {reprStr other}")
  | _ => throw (IO.userError "CREATE2 address test did not suspend")
  let store ← execute "CREATE2 empty init ignores maximal offset"
    (address2Program input creator 0 (wordModulus - 1) 0) (ok (expectedAddress2 creator 0 []))
  require (store[1]? == some (scalar 0)) "empty init expanded caller memory"
  let _ ← execute "CREATE2 range overflow remains a language failure"
    (address2Program [] creator 0 (wordModulus - 16) 32)
    (.inLeft .word (.word Memory.overflowReason))
  pure ()

private structure Invocation where
  depth : Nat := 0
  offset : Nat := 7
  length : Nat := 65
  create2 : Bool := false
  installed : Bool := true
  address : Nat := 0x1234
  fail : Bool := false
  mutate : Bool := false
  tick : Bool := false

private def callbackBody (invocation : Invocation) : Expr :=
  let request := Expr.var 0
  let rejected := LanguageResult.failure Creation.responseType (number 99)
  let result := if invocation.fail then rejected else LanguageResult.success
    (Creation.response (number invocation.address)
      (Creation.requestField 6 request) (Creation.requestField 7 request))
  let result := if invocation.mutate then LocalSequence.discard Creation.responseType
    (Memory.mstore8 (.var 6) (.var 5) (number 7) (number 0xee)) result else result
  let checks := [(0, 0xabc), (1, 17), (2, 77), (4, invocation.depth + 1), (5, 88), (7, invocation.length)]
  let checked : Expr := checks.foldr (fun (index, expected) next =>
    .ifE (.binary .wordEq (Creation.requestField index request) (number expected)) next rejected)
    (.ifE (Creation.requestField 3 request) (if invocation.create2 then result else rejected)
      (if invocation.create2 then rejected else result))
  .letE (.storeCell (.var 1) (.binary .wordAdd (.loadCell (.var 1)) (number 1))) (checked.weakenAt 0)

private def invoke (invocation : Invocation) : Expr :=
  let tick (value : Expr) := if invocation.tick then
    Expr.letE (.storeCell (.var 0) (.binary .wordAdd (.loadCell (.var 0)) (number 1)))
      (value.weakenAt 0) else value
  Creation.invoke (tick (.var 5)) (tick (.var 4)) (tick (.var 3)) (tick (.var 2)) (tick (.var 1))
    (tick (number (2 ^ 200 + 0xabc))) (tick (number invocation.depth))
    (tick (number 17)) (tick (number 77)) (tick (.bool invocation.create2)) (tick (number 88))
    (tick (number invocation.offset)) (tick (number invocation.length))

private def program (input : List UInt8) (invocation : Invocation) : Program :=
  let body := if invocation.installed then
    Expr.letE (.storeCell (.var 1) (.inRight .unit
      (.lambda Creation.requestType (LanguageResult.resultType Creation.responseType) (callbackBody invocation))))
      ((invoke invocation).weakenAt 0) else invoke invocation
  {resultType := LanguageResult.resultType .word, dataDefinitions := Memory.definitions,
   body := .letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes input)))
     (.letE (.newCell .word (number 0))
       (.letE (.newCell WordMapping.type (WordMapping.literal (Memory.packBytes (bytes [0xaa, 0xbb]))))
         (.letE (.newCell .word (number 2))
           (.letE (OptionalCell.allocate Creation.callbackType)
             (.letE (.newCell .word (number 0)) body)))))}

private def entries : Value → Except String WordMapping.Entries
  | .constructed constructor .unit =>
      if constructor == WordMapping.nilConstructor then pure [] else .error "invalid empty map"
  | .constructed constructor (.pair (.pair (.word key) (.word value)) tail) => do
      unless constructor == WordMapping.consConstructor do throw "invalid map constructor"
      pure ((key, value) :: (← entries tail))
  | _ => .error "invalid map value"

private def verify (label : String) (input returned : List UInt8) (size count : Nat) (store : Store) : IO Unit := do
  require (store[0]? == some (WordMapping.encode (Memory.packBytes input))) s!"{label}: memory changed"
  require (store[1]? == some (scalar size)) s!"{label}: memory extent"
  let some mapping := store[2]? | throw (IO.userError s!"{label}: missing return data cell")
  let actual ← match entries mapping with
    | .ok actual => pure actual
    | .error error => throw (IO.userError s!"{label}: {error}")
  let expected := Memory.packBytes returned
  for (key, _) in actual ++ expected do
    require (WordMapping.lookupEntries key actual == WordMapping.lookupEntries key expected)
      s!"{label}: return bytes at packed word {key.val}"
  require (store[3]? == some (scalar returned.length)) s!"{label}: return-data extent"
  require (store[5]? == some (scalar count)) s!"{label}: argument/callback count"

private def transportTests : IO Unit := do
  let input := (List.range 160).map fun index => UInt8.ofNat (index * 7 + 3)
  let payload := (input.drop 7).take 65
  for create2 in [false, true] do
    let compiled := program input {create2, tick := true}
    let store ← execute "CREATE transport fields and exact-once arguments" compiled (ok 0x1234)
    verify "CREATE transport fields and exact-once arguments" input payload 96 14 store
  let compiled := program input {address := 0, mutate := true}
  let store ← execute "CREATE revert bytes preserve input snapshot" compiled (ok 0)
  let changed := input.take 7 ++ bytes [0xee] ++ input.drop 8
  verify "CREATE revert bytes preserve input snapshot" changed payload 96 1 store
  match compiled.runStateful 100 with
  | .outOfFuel checkpoint => match ← resumeChunks 1000 checkpoint with
      | .done value store =>
          require (value == ok 0) "creation transport resume changed result"
          verify "creation transport resume" changed payload 96 1 store
      | other => throw (IO.userError s!"creation transport resume: {reprStr other}")
  | _ => throw (IO.userError "creation transport did not suspend")
  let store ← execute "depth1023 allows child1024" (program input {depth := 1023}) (ok 0x1234)
  verify "depth1023 allows child1024" input payload 96 1 store
  for depth in [1024, wordModulus - 1] do
    let store ← execute "depth refusal clears return data" (program input {depth}) (ok 0)
    verify "depth refusal clears return data" input [] 96 0 store
  let store ← execute "empty init at maximum offset"
    (program input {offset := wordModulus - 1, length := 0}) (ok 0x1234)
  verify "empty init at maximum offset" input [] 0 1 store
  let store ← execute "missing creation callback" (program input {installed := false})
    (.inLeft .word (.word Creation.unavailableReason))
  verify "missing creation callback" input [] 96 0 store
  let store ← execute "creation callback language failure" (program input {fail := true})
    (.inLeft .word (scalar 99))
  verify "creation callback language failure" input [] 96 1 store
  let store ← execute "invalid init range preserves prior return data"
    (program input {offset := wordModulus - 16, length := 32})
    (.inLeft .word (.word Memory.overflowReason))
  verify "invalid init range preserves prior return data" input (bytes [0xaa, 0xbb]) 0 0 store

def run : IO Unit := do
  addressTests
  transportTests
  IO.println "Rust Hull creation tests passed"

end Tests.RustHullCreation
end

section
-- leanmerge: from Solcore.Test.RustHullCreationAccounts
/-! Public contract execution tests for linked constructor and runtime objects.
The byte images below were produced by solc 0.8.35, optimized Yul, Osaka. They
describe the same constructor and runtime operations as the checked Hull trees.
Address and code-hash constants were independently checked with Foundry cast. -/
set_option autoImplicit false
namespace Tests.RustHullCreationAccounts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ident (value : String) : YulExpr := ⟨.ident (name value), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr :=
  ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt :=
  ⟨.expression (call value args), none⟩
private def binding (value : String) (init : YulExpr) : YulStmt :=
  ⟨.letDecl [name value] (some init), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Object" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}

private def runtimeBytes : List UInt8 :=
  [0x36, 0x60, 0x0c, 0x57, 0x5f, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x33, 0xff]
private def initBytes : List UInt8 :=
  [0x60, 0x2a, 0x5f, 0x55, 0x60, 0x0f, 0x80, 0x60, 0x0e, 0x5f, 0x39, 0x5f, 0xf3, 0xfe] ++ runtimeBytes
private def argsInitBytes : List UInt8 :=
  [0x60, 0x20, 0x60, 0x23, 0x5f, 0x39, 0x5f, 0x51, 0x5f, 0x55,
    0x60, 0x0f, 0x80, 0x60, 0x14, 0x5f, 0x39, 0x5f, 0xf3, 0xfe] ++ runtimeBytes
private def revertInitBytes : List UInt8 :=
  [0x61, 0xde, 0xad, 0x5f, 0x52, 0x60, 0x02, 0x60, 0x1e, 0xfd]
private def bytesNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun accum byte => accum * 256 + byte.toNat) 0
private def writeBytes (bytes : List UInt8) : List YulStmt :=
  ((List.range ((bytes.length + 31) / 32)).map fun index =>
    let chunk := (bytes.drop (32 * index)).take 32
    action "mstore" [w (32 * index), w (bytesNat chunk * 256 ^ (32 - chunk.length))])
private def runtimeBody : List YulStmt :=
  [⟨.ifThen (call "calldatasize") [action "selfdestruct" [call "caller"]], none⟩,
    action "mstore" [w 0, call "sload" [w 0]], action "return" [w 0, w 32]]
private def installBody : List YulStmt :=
  writeBytes runtimeBytes ++ [action "return" [w 0, w runtimeBytes.length]]
private def initBody : List YulStmt := [action "sstore" [w 0, w 42]] ++ installBody
private def argsInitBody : List YulStmt :=
  [action "codecopy" [w 0, w argsInitBytes.length, w 32],
    action "sstore" [w 0, call "mload" [w 0]]] ++ installBody
private def revertInitBody : List YulStmt :=
  [action "sstore" [w 0, w 99], action "mstore" [w 0, w 0xdead], action "revert" [w 30, w 2]]
private def definition (body : List YulStmt) (bytes : List UInt8) (isInit := false) :
    AccountRuntime.CodeDefinition :=
  {program := source body, path := ["Object"], bytes := bytes, isInit := isInit}
private def catalog : List AccountRuntime.CodeDefinition :=
  [definition initBody initBytes true, definition runtimeBody runtimeBytes,
    definition argsInitBody argsInitBytes true, definition revertInitBody revertInitBytes true]

private def createAddress : Nat := 0x21e44f0740e8cf48922d40250130b7fa7d305f15
private def nextAddress : Nat := 0x70e557a98d22b20fd7da0ba75118691f181defe4
private def create2Address : Nat := 0xd214e0541c6aba1cc87085b4616d8a220ad1da27
private def runtimeHash : Nat := 0xeeedf27530da124ff00108ae56d27fd186832aec5173f01879721fec8410307d
private def context : Contract.Context := {
  address := word 0xaaaa
  caller := word 0xbbbb
  nonce := word 7
  balance := word 100
  availableGas := some (word 10000000)
  completeWorld := true
}
private def create (value := 17) : YulExpr := call "create" [w value, w 0, w initBytes.length]
private def create2 : YulExpr := call "create2" [w 17, w 0, w initBytes.length, w 7]
private def childCall (inputLength := 0) : YulExpr :=
  call "call" [w 1000000, ident "child", w 0, w 0, w inputLength, w 64, w 32]
private def output (values : List YulExpr) : List YulStmt :=
  (values.zipIdx).map (fun (value, index) => action "mstore" [w (128 + 32 * index), value]) ++
    [action "return" [w 128, w (32 * values.length)]]

private def successBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create, binding "status" childCall,
    action "extcodecopy" [ident "child", w 352, w 3, w 20]] ++
  ((output [ident "child", ident "status", call "mload" [w 64],
    call "extcodesize" [ident "child"], call "balance" [ident "child"],
    call "returndatasize", call "extcodehash" [ident "child"]]).dropLast) ++
  [action "return" [w 128, w 244]]
private def repeatedBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create2, binding "second" create2] ++
  output [ident "child", ident "second", call "extcodesize" [ident "child"]]
private def revertBody : List YulStmt :=
  writeBytes revertInitBytes ++
  [binding "failed" (call "create" [w 17, w 0, w revertInitBytes.length]),
    binding "returnSize" (call "returndatasize"), action "returndatacopy" [w 64, w 0, w 2]] ++
  writeBytes initBytes ++ [binding "child" create] ++
  output [ident "failed", ident "returnSize", call "mload" [w 64], ident "child"]
private def destructionBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create2, binding "status" (childCall 1),
    binding "sizeBeforeEnd" (call "extcodesize" [ident "child"]), binding "second" create2] ++
  output [ident "child", ident "status", ident "sizeBeforeEnd", ident "second",
    call "balance" [ident "child"], call "selfbalance"]
private def argsBody : List YulStmt :=
  writeBytes (argsInitBytes ++ wordBytes 77) ++
  [binding "child" (call "create" [w 17, w 0, w (argsInitBytes.length + 32)]),
    binding "status" childCall] ++
  output [ident "child", ident "status", call "mload" [w 64]]
private def parentBody : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0])
    ([(0, successBody), (1, repeatedBody), (2, revertBody),
      (3, writeBytes initBytes ++ [action "pop" [create], action "revert" [w 0, w 0]]),
      (4, destructionBody), (5, argsBody),
      (6, [action "mstore8" [w 0, w 0xff], action "pop" [call "create" [w 0, w 0, w 1]]])].map
      fun (value, body) => ⟨.number (toString value), body, none⟩)
    (some [action "invalid"]), none⟩]

private def compile (entries := catalog) : IO Contract.CompiledObject :=
  match Contract.compileObject (source parentBody) ["Object"] 4096 none entries with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"creation accounts compile: {reprStr error}")
private def execute (compiled : Contract.CompiledObject) (selector : Nat)
    (supplied := context) (fuel := 10000000) : Contract.Receipt :=
  Contract.runWithReceipt (compiled.instantiate {supplied with calldata := wordBytes selector}) fuel
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8) : IO Unit := do
  require receipt.logs.isEmpty s!"{label}: unexpected logs"
  match receipt.outcome with
  | .returned actual _ => require (actual == expected) s!"{label}: unexpected bytes {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (label : String) (receipt : Contract.Receipt) (address : Nat) : IO AccountState.Account :=
  match receipt.world.find? (·.address == word address) with
  | some result => pure result
  | none => throw (IO.userError s!"{label}: missing account {address}")
private def balance (label : String) (receipt : Contract.Receipt) (address expected : Nat) : IO Unit :=
  require (Core.WordMapping.lookupEntries (word address) receipt.balances == word expected)
    s!"{label}: incorrect balance at {address}"
private def nonce (label : String) (receipt : Contract.Receipt) (address expected : Nat) : IO Unit := do
  let actual ← account label receipt address
  require (actual.nonce == word expected) s!"{label}: incorrect nonce"
private def childState (label : String) (receipt : Contract.Receipt) (address stored : Nat) : IO Unit := do
  let actual ← account label receipt address
  require (actual.code == some runtimeBytes && actual.nonce == word 1)
    s!"{label}: wrong installed code or nonce"
  require (Core.WordMapping.lookupEntries (word 0) actual.storage == word stored)
    s!"{label}: constructor storage lost"
  require (actual.transient.isEmpty && !actual.created && !actual.destroyed)
    s!"{label}: transaction finalization did not clear flags/transient"
private def noPublishedState (label : String) (receipt : Contract.Receipt) : IO Unit :=
  require (receipt.world.isEmpty && receipt.balances.isEmpty && receipt.logs.isEmpty)
    s!"{label}: failed/suspended execution published state"
private def resumeCreation : Nat → Contract.Receipt → IO (Contract.Receipt × Nat)
  | 0, _ => throw (IO.userError "creation checkpoint budget exhausted")
  | remaining + 1, receipt => match receipt.outcome with
      | .outOfFuel state => do
          noPublishedState "creation checkpoint" receipt
          let (result, count) ← resumeCreation remaining (Contract.resumeWithReceipt state 5000)
          pure (result, count + 1)
      | _ => pure (receipt, 0)

def run : IO Unit := do
  let compiled ← compile
  let supplied := {context with accounts := [(word createAddress, word 5)]}
  let expected := words [createAddress, 1, 42, 15, 22, 32, runtimeHash] ++
    runtimeBytes.drop 3 ++ List.replicate 8 0
  let success := execute compiled 0 supplied
  returned "CREATE, CALL and exact child code inspection" success expected
  childState "created runtime" success createAddress 42
  nonce "creator increment" success 0xaaaa 8
  balance "creator debit" success 0xaaaa 83
  balance "prefunded child" success createAddress 22

  let suspended := execute compiled 0 supplied 1000
  noPublishedState "creation checkpoint" suspended
  let (resumed, checkpoints) ← resumeCreation 3000 suspended
  require (checkpoints > 1) "creation did not cross repeated checkpoints"
  returned "creation resume" resumed expected
  childState "creation resume storage/code" resumed createAddress 42
  nonce "creation resume increments once" resumed 0xaaaa 8
  require (success.balances == resumed.balances) "creation resume changed balances"

  let repeated := execute compiled 1
  returned "CREATE2 address and repeated collision" repeated (words [create2Address, 0, 15])
  childState "CREATE2 retained runtime" repeated create2Address 42
  nonce "CREATE2 collision retains second nonce increment" repeated 0xaaaa 9
  balance "CREATE2 collision refunds value" repeated 0xaaaa 83

  let reverted := execute compiled 2
  returned "constructor revert bytes and next CREATE nonce" reverted
    (words [0, 2, 0xdead * 256 ^ 30, nextAddress])
  require (!(reverted.world.any (·.address == word createAddress))) "reverted constructor left an account"
  childState "CREATE after reverted constructor" reverted nextAddress 42
  nonce "reverted constructor nonce remains consumed" reverted 0xaaaa 9
  balance "reverted constructor value refunded" reverted 0xaaaa 83

  let collision := execute compiled 0 {context with world := [{address := word createAddress, nonce := word 1}]}
  -- CREATE returns zero on collision. Subsequent empty-account CALL succeeds and
  -- all zero-address observations remain empty; its EXTCODEHASH is zero.
  returned "preexisting nonce collision" collision (words [0, 1, 0, 0, 0, 0, 0] ++ List.replicate 20 0)
  nonce "collision increments creator" collision 0xaaaa 8
  nonce "collision keeps target" collision createAddress 1
  balance "collision retains sender value" collision 0xaaaa 100

  let destroyed := execute compiled 4
  returned "SELFDESTRUCT keeps code until transaction end and CREATE2 still collides" destroyed
    (words [create2Address, 1, 15, 0, 0, 100])
  require (!(destroyed.world.any (·.address == word create2Address))) "created-and-destroyed account survived finalization"
  balance "destroyed target balance cleared" destroyed create2Address 0
  balance "SELFDESTRUCT beneficiary credited" destroyed 0xaaaa 100
  nonce "pending deletion blocks recreation" destroyed 0xaaaa 9

  let args := execute compiled 5
  returned "constructor reads suffix through CODECOPY" args (words [createAddress, 1, 77])
  childState "constructor suffix storage" args createAddress 77

  let parentRevert := execute compiled 3
  noPublishedState "parent revert discards created child" parentRevert
  match parentRevert.outcome with
  | .reverted [] => pure ()
  | other => throw (IO.userError s!"parent revert after creation: {reprStr other}")
  let static := execute compiled 0 {context with isStatic := true}
  noPublishedState "static CREATE" static
  match static.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"static CREATE: {reprStr other}")
  let static2 := execute compiled 1 {context with isStatic := true}
  noPublishedState "static CREATE2" static2
  match static2.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"static CREATE2: {reprStr other}")
  let unknown := execute compiled 6
  noPublishedState "unknown init bytes" unknown
  match unknown.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "unknown init has incorrect failure"
  | other => throw (IO.userError s!"unknown init: {reprStr other}")
  let ambiguous ← compile (definition initBody (initBytes.take 4) true :: catalog)
  let ambiguous := execute ambiguous 0
  noPublishedState "ambiguous init prefix" ambiguous
  match ambiguous.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "ambiguous init has incorrect failure"
  | other => throw (IO.userError s!"ambiguous init prefix: {reprStr other}")
  IO.println "Rust Hull creation account tests passed"

end Tests.RustHullCreationAccounts
end

section
-- leanmerge: from Solcore.Test.RustHullCreationAddressVectors
/-! The independent CREATE and CREATE2 address specification derives the 11
reference vectors in `Tests/Fixtures/EvmAccounts/address-vectors.json`, which
were computed with `cast` and Python RLP. They cover every RLP nonce encoding,
including EIP-2681's largest nonce, and CREATE2 init code of one and four
bytes. Each digest is evaluated in the kernel. -/
set_option autoImplicit false
namespace Tests.RustHullCreationAddressVectors
open Solcore Solcore.Frontend.RustHull

private abbrev w := Core.Word.ofNatModulo

/-- The specification derives the reference CREATE address of a short preimage. -/
theorem create_vector {creator nonce expected : Core.Word}
    (short : (CreationAddressSemantics.createPreimage creator nonce).length < 136)
    (computed : CreationAddressSemantics.address
      (CreationPreimage.shortDigest (CreationAddressSemantics.createPreimage creator nonce)) = expected) :
    CreationAddressSemantics.Derived creator nonce [] Core.Word.zero .create expected := by
  rw [← computed]
  exact .create (CreationPreimage.shortDigest_keccak short)

/-- The specification derives the reference CREATE2 address of short init code. -/
theorem create2_vector {creator salt expected : Core.Word} {init : CreationAddressSemantics.Bytes}
    (short : init.length < 136)
    (computed : CreationAddressSemantics.address (CreationPreimage.shortDigest
      (CreationAddressSemantics.create2Preimage creator salt (CreationPreimage.shortDigest init))) = expected) :
    CreationAddressSemantics.Derived creator Core.Word.zero (CreationAddressSemantics.stored init) (w init.length)
      (.create2 salt) expected := by
  rw [← computed]
  exact .create2 (CreationPreimage.shortDigest_keccak short)
    (CreationPreimage.shortDigest_keccak (by rw [CreationPreimage.create2Preimage_length]; decide))

private def deadbeef : Core.Word := w 0xdeadbeef00000000000000000000000000000000

theorem create_nonce_0 : CreationAddressSemantics.Derived deadbeef (w 0) [] Core.Word.zero .create
    (w 0xf2048c36a5536fea3bc71d49ed59f2c65c546eea) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_1 : CreationAddressSemantics.Derived deadbeef (w 1) [] Core.Word.zero .create
    (w 0x054dd934335ea61232ae4c051f8bf20e540f8291) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_127 : CreationAddressSemantics.Derived deadbeef (w 127) [] Core.Word.zero .create
    (w 0x7feb088e1893d4a1087288d386c07252abb3c02e) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_128 : CreationAddressSemantics.Derived deadbeef (w 128) [] Core.Word.zero .create
    (w 0x2297787b25b800d655071345a1d3a7951404b50c) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_255 : CreationAddressSemantics.Derived deadbeef (w 255) [] Core.Word.zero .create
    (w 0xc8d17a8bdb6001525f8594e3ca4413d4bd644605) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_256 : CreationAddressSemantics.Derived deadbeef (w 256) [] Core.Word.zero .create
    (w 0xa0ddf5980551b5ec83721bcf168785ac3cedb183) := create_vector (by decide +kernel) (by decide +kernel)
theorem create_nonce_largest : CreationAddressSemantics.Derived deadbeef (w 18446744073709551615) [] Core.Word.zero
    .create (w 0x66e93872e94cc56d1da3bb63f81dabd9c1d6c125) := create_vector (by decide +kernel) (by decide +kernel)
theorem create2_zero_creator : CreationAddressSemantics.Derived (w 0) Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 0)) (w 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_zero_salt : CreationAddressSemantics.Derived deadbeef Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 0)) (w 0xb928f69bb1d91cd65274e3c79d8986362984fda3) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_salt : CreationAddressSemantics.Derived deadbeef Core.Word.zero (CreationAddressSemantics.stored [0])
    (w 1) (.create2 (w 22207167547627365064083290255604625247830016)) (w 0xf2a2934e8506d97a2cee99962533f9729676ae24) :=
  create2_vector (by decide) (by decide +kernel)
theorem create2_init : CreationAddressSemantics.Derived (w 0xdeadbeef) Core.Word.zero
    (CreationAddressSemantics.stored [0xde, 0xad, 0xbe, 0xef]) (w 4) (.create2 (w 3405691582))
    (w 0x60f3f640a8508fc6a86d45df051962668e1e8ac7) :=
  create2_vector (by decide) (by decide +kernel)

end Tests.RustHullCreationAddressVectors
end

section
-- leanmerge: from Solcore.Test.RustHullCreationAdmittedCorrespondence
/-! Admitted CREATE and CREATE2 attempts that run no init frame reach the
actual lowering, transport and installed create handler through the call-mode
public theorem. Each scenario stores the attempt's result word and returns it.
Two deployments of empty init code create a new account with nonce one, one of
them with an endowment; a nonzero nonce and nonempty code at the derived
address are collisions that return zero. Every attempt advances the creator
nonce. The derived addresses are checked in the kernel against the
independent RLP and Keccak specification. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationAdmittedCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | deployed | deployed2 | collision | collision2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def emptyHash : Core.Word := CreationPreimage.shortDigest []
def createTarget : Core.Word := w 515330412878651974478734746372204808145222434547
def create2Target : Core.Word := w 376623410840471690759715731732645848578652475442

theorem createTarget_derived : CreationAddressSemantics.address
    (CreationPreimage.shortDigest (CreationAddressSemantics.createPreimage Core.Word.zero (w 1))) = createTarget := by
  decide +kernel

theorem create2Target_derived : CreationAddressSemantics.address
    (CreationPreimage.shortDigest (CreationAddressSemantics.create2Preimage Core.Word.zero (w 7) emptyHash)) =
      create2Target := by
  decide +kernel

def rootBytes : List UInt8 := [0]
def target : Scenario → Core.Word
  | .deployed | .collision => createTarget
  | .deployed2 | .collision2 => create2Target
/-- An account at the CREATE address with a nonzero nonce, and one at the
CREATE2 address with code. -/
def occupant : Scenario → List AccountState.Account
  | .collision => [{address := createTarget, nonce := w 1}]
  | .collision2 => [{address := create2Target, code := some [254]}]
  | _ => []
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 3, availableGas := some (w 100), completeWorld := true, world := occupant scenario}
def scheme : Scenario → CreationAddressSemantics.Scheme
  | .deployed | .collision => .create
  | .deployed2 | .collision2 => .create2 (w 7)
def endowment : Scenario → Core.Word
  | .deployed => w 2
  | _ => w 0
def invoked : Scenario → Expr
  | .deployed => call .word "create" [word "2", word "0", word "0"]
  | .collision => call .word "create" [word "0", word "0", word "0"]
  | .deployed2 | .collision2 => call .word "create2" [word "0", word "0", word "0", word "7"]
def stored (scenario : Scenario) : Expr := call .unit "mstore" [word "0", invoked scenario]
def returned : Expr := call .unit "return" [word "0", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩

/-- The creator's record in the initial world. -/
def creatorAccount (object : Contract.CompiledObject) (scenario : Scenario) : AccountState.Account :=
  match StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external) true with
  | .ok account => account
  | .error _ => {address := Core.Word.zero}

def deploys : Scenario → Bool
  | .deployed | .deployed2 => true
  | _ => false
def endowed : Scenario → StorageSemantics.Words
  | .deployed => [(w 0, w 1), (createTarget, w 2)]
  | _ => [(w 0, w 3)]
def created (scenario : Scenario) : Core.Word := if deploys scenario then target scenario else Core.Word.zero

/-- The frame state after the attempt: the creator nonce advanced, and either
a new account with its endowment or a collision. -/
def afterAttempt (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let advanced := CreationSemantics.advanced (initial object scenario).external (creatorAccount object scenario)
  if deploys scenario then ⟨[], CreationSemantics.deployed advanced (target scenario) (endowed scenario) Core.Word.zero⟩
  else ⟨[], CreationSemantics.refused advanced Core.Word.zero⟩
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterAttempt object scenario)
    (MemorySemantics.mstore (frame (afterAttempt object scenario)).memory (w 0) (created scenario)).2
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 0) (w 32)).2)}⟩
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)

private theorem address_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    (frame (initial object scenario)).storage.address = Contract.normalizeAddress Core.Word.zero := rfl

private theorem creator_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.creator (initial object scenario).external = Core.Word.zero := by
  change (frame (initial object scenario)).storage.address.bitAnd _ = _
  rw [address_zero]
  decide

private theorem creator_found (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.complete = .ok (creatorAccount object scenario) := by
  have complete : (frame (initial object scenario)).storage.complete = true := by cases scenario <;> rfl
  rw [complete]
  unfold creatorAccount
  cases found : StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external) true with
  | ok account => rfl
  | error reason =>
      unfold StorageSemantics.get at found
      split at found <;> simp at found

private theorem creator_nonce (object : Contract.CompiledObject) (scenario : Scenario) :
    (creatorAccount object scenario).nonce = w 1 := by
  cases scenario <;> rfl


private theorem balances_initial (object : Contract.CompiledObject) (scenario : Scenario) :
    (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      [(Contract.normalizeAddress Core.Word.zero, w 3)] := rfl

private theorem admission (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admission (endowment scenario) (w 0) (w 0) (initial object scenario).external Core.Word.zero
      (creatorAccount object scenario) := by
  refine ⟨rfl, by decide, ⟨w 100, rfl⟩, rfl, ?_, ?_, creator_found object scenario, ?_⟩
  · change Core.Word.zero.val < CreationSemantics.depthLimit
    decide
  · change (endowment scenario).val ≤ (StorageSemantics.readWord (CreationSemantics.creator (initial object scenario).external)
      (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances).val
    rw [creator_zero, balances_initial]
    cases scenario <;> decide
  · rw [creator_nonce]
    decide


private theorem advanced_lookup (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.lookup (target scenario)
      (CreationSemantics.frame (CreationSemantics.advanced (initial object scenario).external
        (creatorAccount object scenario))).storage.world = (occupant scenario).head? := by
  change StorageSemantics.lookup (target scenario) (StorageSemantics.put
    (CreationSemantics.creator (initial object scenario).external) _ _) = _
  rw [creator_zero]
  cases scenario <;> rfl

private theorem transferred (object : Contract.CompiledObject) (scenario : Scenario) :
    AccountCallSemantics.transfer (CreationSemantics.creator (initial object scenario).external) (target scenario)
      (endowment scenario) (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      .ok (endowed scenario) := by
  rw [creator_zero, balances_initial]
  cases scenario <;> rfl


private theorem derived_create (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) .create createTarget := by
  rw [creator_zero, creator_nonce, ← createTarget_derived]
  exact .create (CreationPreimage.shortDigest_keccak (by decide +kernel))

private theorem derived_create2 (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) (.create2 (w 7)) create2Target := by
  rw [creator_zero, ← create2Target_derived]
  exact .create2 (initHash := emptyHash) (.last _ _ _ (by decide)) (CreationPreimage.shortDigest_keccak (by decide +kernel))

/-- The independent admitted rule of each attempt. -/
private theorem admitted_rule (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admitted (scheme scenario) (endowment scenario) (w 0) (w 0) (initial object scenario).external
      (.value (.word (created scenario))) (afterAttempt object scenario).external := by
  have admitted := admission object scenario
  have looked := advanced_lookup object scenario
  have moved := transferred object scenario
  cases scenario
  · exact .deployed admitted (.empty _ _ _ _) (derived_create object _) looked rfl rfl moved
  · exact .deployed admitted (.empty _ _ _ _) (derived_create2 object _) looked rfl rfl moved
  · exact .collision admitted (.empty _ _ _ _) (derived_create object _) looked (.inl (by decide))
  · exact .collision admitted (.empty _ _ _ _) (derived_create2 object _) looked (.inr (by decide))

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (initial object scenario)
      (.value (.word (created scenario))) (afterAttempt object scenario) := by
  have computed := admitted_rule object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "2") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (initial object scenario)
      (.value .unit) (afterStore object scenario) := by
  cases scenario
  all_goals
    apply Semantics.EvalExpr.call rfl
    · exact .cons (.word (text := "0") rfl) (.cons (attempt_source object _) .nil)
    · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] returned (afterStore object scenario) result
      (finalState object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "0") rfl) (.cons (.word (text := "32") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
    (.expression rfl (store_source object scenario))
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario))
    (by intro impossible; cases impossible)


def usedNames : List String := ["mstore", "create", "create2", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (texts : List String) (available : supported name) (notFunction : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (texts.map word)) := by
  apply ExecutableExpression.external available notFunction
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "create" ["2", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["0", "32"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) (scenario : Scenario) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object (context scenario) [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for admitted CREATE and CREATE2
attempts without an init frame: two deployments of empty init code, one with
an endowment, and two collisions. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def addressBytes (value : Core.Word) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value.val / 256 ^ (31 - index) % 256)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"admitted creation: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"admitted creation: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes storage =>
        let creatorRecord := receipt.world.find? (·.address == Core.Word.zero)
        let targetRecord := receipt.world.find? (·.address == target scenario)
        let targetExpected := if deploys scenario || scenario = .collision then some (w 1) else some (w 0)
        unless bytes == addressBytes (created scenario) && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == endowed scenario && receipt.world.length == 2 &&
            creatorRecord.map (·.nonce) == some (w 2) && targetRecord.map (·.nonce) == targetExpected &&
            targetRecord.map (·.code) == some (if scenario = .collision2 then some [254] else some []) do
          throw (IO.userError s!"admitted creation: wrong receipt for {reprStr scenario}: {reprStr receipt}")
    | outcome =>
        throw (IO.userError s!"admitted creation: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.deployed, .deployed2, .collision, .collision2] do
    check scenario

end Tests.RustHullCreationAdmittedCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCreationCorrespondence
/-! CREATE and CREATE2 attempts refused before init code runs reach the actual
lowering, transport and installed create handler through the call-mode public
theorem. Each scenario writes a byte, attempts a creation, stores its result
and returns two bytes. A static frame or oversized init code halts the frame,
a missing gas observation or an unaddressable init range faults, and an
insufficient endowment or an exhausted nonce returns zero without changing
the creator's nonce. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | staticFrame | oversized | missingGas | inputOverflow | underfunded | nonceExhausted
  | oversized2 | underfunded2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def rootBytes : List UInt8 := [0]
def context : Scenario → Contract.Context
  | .staticFrame => {balance := w 3, availableGas := some (w 100), completeWorld := true, isStatic := true}
  | .missingGas => {balance := w 3, completeWorld := true}
  | .nonceExhausted => {balance := w 3, availableGas := some (w 100), completeWorld := true, nonce := w (2 ^ 64 - 1)}
  | _ => {balance := w 3, availableGas := some (w 100), completeWorld := true}

/-- Endowment, init offset and init length of each attempt. -/
def value : Scenario → Core.Word
  | .underfunded | .underfunded2 => w 5
  | _ => w 0
def offset : Scenario → Core.Word
  | .inputOverflow => w (Core.wordModulus - 16)
  | _ => w 0
def length : Scenario → Core.Word
  | .oversized | .oversized2 => w 49153
  | .inputOverflow => w 32
  | .underfunded | .underfunded2 | .nonceExhausted => w 2
  | _ => w 1

def invoked : Scenario → Expr
  | .staticFrame => call .word "create" [word "0", word "0", word "1"]
  | .oversized => call .word "create" [word "0", word "0", word "49153"]
  | .missingGas => call .word "create" [word "0", word "0", word "1"]
  | .inputOverflow => call .word "create" [word "0",
      word "115792089237316195423570985008687907853269984665640564039457584007913129639920", word "32"]
  | .underfunded => call .word "create" [word "5", word "0", word "2"]
  | .nonceExhausted => call .word "create" [word "0", word "0", word "2"]
  | .oversized2 => call .word "create2" [word "0", word "0", word "49153", word "7"]
  | .underfunded2 => call .word "create2" [word "5", word "0", word "2", word "7"]
def seed : Expr := call .unit "mstore8" [word "1", word "171"]
def stored (scenario : Scenario) : Expr := call .unit "mstore8" [word "2", invoked scenario]
def returned : Expr := call .unit "return" [word "1", word "2"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression seed, expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def withMemory (state : SourceState) (memory : MemorySemantics.State) : SourceState :=
  ⟨[], {state.external with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.external.runtime
    {frame state with memory := memory})}⟩
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩
def seeded : MemorySemantics.State := (MemorySemantics.mstore8 {} (w 1) (w 171)).2
def memoryWritten (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (initial object scenario) seeded

/-- The frame state after the attempt: halted, unchanged, or refused with the
init range covered and return data cleared. -/
def afterAttempt (object : Contract.CompiledObject) : Scenario → SourceState
  | .staticFrame => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .staticFrame).external).2⟩
  | .oversized => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .oversized).external).2⟩
  | .oversized2 => ⟨[], (RuntimeCallEffectsSemantics.invalid (memoryWritten object .oversized2).external).2⟩
  | .missingGas => memoryWritten object .missingGas
  | .inputOverflow => memoryWritten object .inputOverflow
  | scenario => ⟨[], CreationSemantics.refused (memoryWritten object scenario).external (w 32)⟩
def attemptResult : Scenario → Semantics.Result Semantics.Value
  | .staticFrame | .oversized | .oversized2 => .fault (.language Core.Word.maximum)
  | .missingGas => .fault (.language (w 9))
  | .inputOverflow => MemorySemantics.overflow
  | _ => .value (.word (w 0))
def afterStore (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  withMemory (afterAttempt object scenario) (MemorySemantics.mstore8 (frame (afterAttempt object scenario)).memory (w 2) (w 0)).2
def finished (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  let state := (afterStore object scenario).external
  ⟨[], {state with runtime := (RuntimeReturnDataEffectsSemantics.withRuntime state.runtime
    (TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 1 (w 1) (w 2)).2)}⟩

/-- Refused attempts continue to the return; the others stop the frame. -/
def refuses : Scenario → Bool
  | .underfunded | .nonceExhausted | .underfunded2 => true
  | _ => false
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  if refuses scenario then finished object scenario else afterAttempt object scenario
def result (scenario : Scenario) : Semantics.Result Semantics.Value :=
  if refuses scenario then .fault (.language Core.Word.maximum) else attemptResult scenario

private theorem seed_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] seed (initial object scenario) (.value .unit)
      (memoryWritten object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "171") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

/-- The independent refusal of each attempt. -/
private theorem refused (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Refused (value scenario) (offset scenario) (length scenario)
      (memoryWritten object scenario).external (attemptResult scenario) (afterAttempt object scenario).external := by
  have gas : ∀ scenario, scenario ≠ .missingGas → scenario ≠ .staticFrame →
      CreationSemantics.availableGas (memoryWritten object scenario).external = some (w 100) := by
    intro scenario notMissing notStatic
    cases scenario <;> first | rfl | contradiction
  cases scenario
  · exact .staticFrame _ rfl
  · exact .oversized _ rfl (by decide)
  · exact .missingGas _ rfl (by decide) rfl
  · exact .inputOverflow _ rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w (Core.wordModulus - 16)) (w 32) = none; decide)
  · apply CreationSemantics.Refused.underfunded rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
    change (w 3).val < (w 5).val
    decide
  · apply CreationSemantics.Refused.nonceExhausted rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
      (by change (w 0).val ≤ (w 3).val; decide) rfl
    change CreationSemantics.maxNonce ≤ (w (2 ^ 64 - 1)).val
    decide
  · exact .oversized _ rfl (by decide)
  · apply CreationSemantics.Refused.underfunded rfl (by decide) (gas _ (by decide) (by decide))
      (by change MemorySemantics.touchSize? (w 32) (w 0) (w 2) = some (w 32); decide)
      (by change Core.Word.zero.val < CreationSemantics.depthLimit; decide)
    change (w 3).val < (w 5).val
    decide

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (memoryWritten object scenario)
      (attemptResult scenario) (afterAttempt object scenario) := by
  have computed := refused object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "49153") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "1") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "115792089237316195423570985008687907853269984665640564039457584007913129639920") rfl)
        (.cons (.word (text := "32") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "5") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl) .nil)))
      (.external (by rfl) rfl (.create computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "49153") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2 (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "5") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "2") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2 (salt := w 7) computed))

private theorem store_source (object : Contract.CompiledObject) (scenario : Scenario) (refusing : refuses scenario = true) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (memoryWritten object scenario)
      (.value .unit) (afterStore object scenario) := by
  cases scenario
  all_goals first
    | exact absurd refusing (by decide)
    | apply Semantics.EvalExpr.call rfl
      · exact .cons (.word (text := "2") rfl) (.cons (attempt_source object _) .nil)
      · exact .external (by rfl) rfl
          (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime rfl))))))))

private theorem store_fault (object : Contract.CompiledObject) (scenario : Scenario) (stopping : refuses scenario = false) :
    ∃ reason, attemptResult scenario = .fault reason ∧
      Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (memoryWritten object scenario)
        (.fault reason) (afterAttempt object scenario) := by
  have attempted := attempt_source object scenario
  obtain ⟨reason, faulted⟩ : ∃ reason, attemptResult scenario = .fault reason := by
    cases scenario <;> first | exact ⟨_, rfl⟩ | cases stopping
  rw [faulted] at attempted
  exact ⟨reason, faulted, .callFault rfl (.cons (.word (text := "2") rfl) (.fault attempted))⟩

private theorem return_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] returned (afterStore object scenario)
      (.fault (.language Core.Word.maximum)) (finished object scenario) := by
  apply Semantics.EvalExpr.call rfl
  · exact .cons (.word (text := "1") rfl) (.cons (.word (text := "2") rfl) .nil)
  · exact .external (by rfl) rfl (.runtime (.runtime (.runtime (.runtime (.runtime (.runtime (.termination rfl)))))))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) (result scenario) (finalState object scenario) := by
  cases refusing : refuses scenario
  · obtain ⟨reason, faulted, attempted⟩ := store_fault object scenario refusing
    have resulted : result scenario = .fault reason := by simp [result, refusing, faulted]
    have final : finalState object scenario = afterAttempt object scenario := by simp [finalState, refusing]
    rw [resulted, final]
    apply Semantics.EvalFunction.body (control := .fault reason) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (seed_source object scenario))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl attempted)
      (by intro impossible; cases impossible)
  · have resulted : result scenario = .fault (.language Core.Word.maximum) := by simp [result, refusing]
    have final : finalState object scenario = finished object scenario := by simp [finalState, refusing]
    rw [resulted, final]
    apply Semantics.EvalFunction.body (control := .fault _) rfl
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (seed_source object scenario))
    apply Semantics.EvalStatements.next (by intros; intro impossible; cases impossible)
      (.expression rfl (store_source object scenario refusing))
    exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (return_source object scenario))
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore8", "create", "create2", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (texts : List String) (available : supported name) (notFunction : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (texts.map word)) := by
  apply ExecutableExpression.external available notFunction
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · exact atoms _ .unit "mstore8" ["1", "171"] (available _ (by simp [usedNames])) (by rfl)
  · apply ExecutableExpression.external (name := "mstore8") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "create" ["0", "0", "1"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "49153"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0",
            "115792089237316195423570985008687907853269984665640564039457584007913129639920", "32"]
            (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["5", "0", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["0", "0", "2"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "49153", "7"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["5", "0", "2", "7"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["1", "2"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store8, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) (scenario : Scenario) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object (context scenario) [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for every refusal reachable from
the outermost frame. The depth refusal needs a frame at depth 1024. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) (result scenario)
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def expectedNonce (scenario : Scenario) : Core.Word :=
  if scenario = .nonceExhausted then w (2 ^ 64 - 1) else w 1

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"creation correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"creation correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match scenario, receipt.outcome with
    | .staticFrame, .invalid | .oversized, .invalid | .oversized2, .invalid => pure ()
    | .missingGas, .languageFailure reason =>
        unless reason == .word (w 9) do
          throw (IO.userError s!"creation correspondence: wrong gas fault: {reprStr reason}")
    | .inputOverflow, .languageFailure reason =>
        unless reason == .word Memory.overflowReason do
          throw (IO.userError s!"creation correspondence: wrong range fault: {reprStr reason}")
    | _, .returned bytes storage =>
        let account := receipt.world.find? (·.address == Core.Word.zero)
        unless refuses scenario && bytes == [171, 0] && storage.isEmpty && receipt.logs.isEmpty &&
            receipt.balances == [(w 0, w 3)] && receipt.world.length == 1 &&
            account.map (·.nonce) == some (expectedNonce scenario) do
          throw (IO.userError s!"creation correspondence: wrong refusal for {reprStr scenario}: {reprStr receipt}")
    | _, outcome =>
        throw (IO.userError s!"creation correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.staticFrame, .oversized, .missingGas, .inputOverflow, .underfunded,
      .nonceExhausted, .oversized2, .underfunded2] do
    check scenario

end Tests.RustHullCreationCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullCreationFaultCorrespondence
/-! Admitted CREATE and CREATE2 attempts that fault after the creator nonce
advance reach the actual lowering, transport and installed create handler
through the call-mode public theorem. Each scenario stores the attempt's result
word and returns it; the attempt faults first and stops the frame. A target
absent from an incomplete world and a recorded target with unknown code are
language fault 7. An endowment that would overflow the target balance is
language fault 12. The faults restore the checkpoint taken after the nonce
advance. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullCreationFaultCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence
open Tests.RustHullCreationAdmittedCorrespondence (emptyHash createTarget create2Target createTarget_derived
  create2Target_derived rootBytes)

inductive Scenario where
  | absent | unknownCode | overflow | overflow2
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def word (text : String) : Expr := ⟨.word, .word text, none⟩
private def call (type : Ty) (name : String) (arguments : List Expr) : Expr := ⟨type, .call name arguments, none⟩
private def expression (value : Expr) : Stmt := ⟨.expression value, none⟩

def target : Scenario → Core.Word
  | .absent | .overflow => createTarget
  | .unknownCode | .overflow2 => create2Target
/-- The CREATE2 target is recorded with a zero nonce and unknown code. -/
def occupant : Scenario → List AccountState.Account
  | .unknownCode => [{address := create2Target, code := none}]
  | _ => []
/-- The overflow targets already hold the largest balance. -/
def held : Scenario → Core.WordMapping.Entries
  | .overflow => [(createTarget, w (Core.wordModulus - 1))]
  | .overflow2 => [(create2Target, w (Core.wordModulus - 1))]
  | _ => []
def context (scenario : Scenario) : Contract.Context :=
  {balance := w 3, availableGas := some (w 100), completeWorld := scenario != .absent,
    world := occupant scenario, accounts := held scenario}
def scheme : Scenario → CreationAddressSemantics.Scheme
  | .absent | .overflow => .create
  | .unknownCode | .overflow2 => .create2 (w 7)
def endowment : Scenario → Core.Word
  | .overflow | .overflow2 => w 1
  | _ => w 0
def reason : Scenario → Core.Word
  | .absent | .unknownCode => w 7
  | .overflow | .overflow2 => w 12
def invoked : Scenario → Expr
  | .absent => call .word "create" [word "0", word "0", word "0"]
  | .overflow => call .word "create" [word "1", word "0", word "0"]
  | .unknownCode => call .word "create2" [word "0", word "0", word "0", word "7"]
  | .overflow2 => call .word "create2" [word "1", word "0", word "0", word "7"]
def stored (scenario : Scenario) : Expr := call .unit "mstore" [word "0", invoked scenario]
def returned : Expr := call .unit "return" [word "0", word "32"]
def code (scenario : Scenario) : CodeBlock := {
  stmts := [expression (stored scenario), expression returned], functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Creator" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] {} 1 (some rootBytes)

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def frame (state : SourceState) := state.external.runtime.runtime.runtime.runtime.runtime
def initial (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext (context scenario))⟩

/-- The creator's record in the initial world. -/
def creatorAccount (object : Contract.CompiledObject) (scenario : Scenario) : AccountState.Account :=
  match StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world with
  | some account => account
  | none => {address := Core.Word.zero}

/-- The frame state after the attempt: only the creator nonce advance remains,
memory covers the empty init range and return data is cleared. -/
def finalState (object : Contract.CompiledObject) (scenario : Scenario) : SourceState :=
  ⟨[], CreationSemantics.refused
    (CreationSemantics.advanced (initial object scenario).external (creatorAccount object scenario)) Core.Word.zero⟩
def result (scenario : Scenario) : Semantics.Result Semantics.Value := .fault (.language (reason scenario))

private theorem address_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    (frame (initial object scenario)).storage.address = Contract.normalizeAddress Core.Word.zero := rfl

private theorem creator_zero (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.creator (initial object scenario).external = Core.Word.zero := by
  change (frame (initial object scenario)).storage.address.bitAnd _ = _
  rw [address_zero]
  decide

private theorem creator_lookup (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world = some (creatorAccount object scenario) := by
  unfold creatorAccount
  cases looked : StorageSemantics.lookup (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.world with
  | some account => rfl
  | none =>
      rw [creator_zero] at looked
      cases scenario <;> cases looked

private theorem creator_found (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.get (frame (initial object scenario)).storage.world
      (CreationSemantics.creator (initial object scenario).external)
      (frame (initial object scenario)).storage.complete = .ok (creatorAccount object scenario) := by
  simp only [StorageSemantics.get, creator_lookup]

private theorem creator_nonce (object : Contract.CompiledObject) (scenario : Scenario) :
    (creatorAccount object scenario).nonce = w 1 := by
  unfold creatorAccount
  rw [creator_zero]
  cases scenario <;> rfl

private theorem balances_initial (object : Contract.CompiledObject) (scenario : Scenario) :
    (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      held scenario ++ [(Contract.normalizeAddress Core.Word.zero, w 3)] := by
  cases scenario <;> rfl

private theorem admission (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admission (endowment scenario) (w 0) (w 0) (initial object scenario).external Core.Word.zero
      (creatorAccount object scenario) := by
  refine ⟨rfl, by decide, ⟨w 100, rfl⟩, rfl, ?_, ?_, creator_found object scenario, ?_⟩
  · change Core.Word.zero.val < CreationSemantics.depthLimit
    decide
  · change (endowment scenario).val ≤ (StorageSemantics.readWord (CreationSemantics.creator (initial object scenario).external)
      (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances).val
    rw [creator_zero, balances_initial]
    cases scenario <;> decide
  · rw [creator_nonce]
    decide

private theorem advanced_lookup (object : Contract.CompiledObject) (scenario : Scenario) :
    StorageSemantics.lookup (target scenario)
      (CreationSemantics.frame (CreationSemantics.advanced (initial object scenario).external
        (creatorAccount object scenario))).storage.world = (occupant scenario).head? := by
  change StorageSemantics.lookup (target scenario) (StorageSemantics.put
    (CreationSemantics.creator (initial object scenario).external) _ _) = _
  rw [creator_zero]
  cases scenario <;> rfl

private theorem overflowed (object : Contract.CompiledObject) (scenario : Scenario)
    (overflowing : scenario = .overflow ∨ scenario = .overflow2) :
    AccountCallSemantics.transfer (CreationSemantics.creator (initial object scenario).external) (target scenario)
      (endowment scenario) (RuntimeCallEffectsSemantics.shared (initial object scenario).external).balances =
      .error (w 12) := by
  rw [creator_zero, balances_initial]
  rcases overflowing with rfl | rfl <;> rfl

private theorem derived_create (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) .create createTarget := by
  rw [creator_zero, creator_nonce, ← createTarget_derived]
  exact .create (CreationPreimage.shortDigest_keccak (by decide +kernel))

private theorem derived_create2 (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationAddressSemantics.Derived (CreationSemantics.creator (initial object scenario).external)
      (creatorAccount object scenario).nonce [] (w 0) (.create2 (w 7)) create2Target := by
  rw [creator_zero, ← create2Target_derived]
  exact .create2 (initHash := emptyHash) (.last _ _ _ (by decide)) (CreationPreimage.shortDigest_keccak (by decide +kernel))

/-- The independent admitted rule of each attempt. -/
private theorem admitted_rule (object : Contract.CompiledObject) (scenario : Scenario) :
    CreationSemantics.Admitted (scheme scenario) (endowment scenario) (w 0) (w 0) (initial object scenario).external
      (result scenario) (finalState object scenario).external := by
  have admitted := admission object scenario
  have looked := advanced_lookup object scenario
  cases scenario
  · exact .unknown admitted (.empty _ _ _ _) (derived_create object _) (.absent looked rfl)
  · exact .unknown admitted (.empty _ _ _ _) (derived_create2 object _) (.unknownCode looked rfl rfl)
  · exact .overflow admitted (.empty _ _ _ _) (derived_create object _) looked rfl
      (overflowed object _ (.inl rfl))
  · exact .overflow admitted (.empty _ _ _ _) (derived_create2 object _) looked rfl
      (overflowed object _ (.inr rfl))

private theorem attempt_source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (invoked scenario) (initial object scenario)
      (result scenario) (finalState object scenario) := by
  have computed := admitted_rule object scenario
  cases scenario
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))
  · exact .call rfl (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl) .nil)))
      (.external (by rfl) rfl (.createAdmitted computed))
  · exact .call rfl (.cons (.word (text := "1") rfl) (.cons (.word (text := "0") rfl) (.cons (.word (text := "0") rfl)
      (.cons (.word (text := "7") rfl) .nil))))
      (.external (by rfl) rfl (.create2Admitted (salt := w 7) computed))

private theorem store_fault (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalExpr (functions scenario) effects [] (stored scenario) (initial object scenario)
      (result scenario) (finalState object scenario) :=
  .callFault rfl (.cons (.word (text := "0") rfl) (.fault (attempt_source object scenario)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object scenario) (result scenario) (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault (.language (reason scenario))) rfl
  exact .stop (by intros; intro impossible; cases impossible) (.expressionFault rfl (store_fault object scenario))
    (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "create", "create2", "return"]

private theorem atoms {supported : String → Prop} (functions : List Function) (type : Ty) (name : String)
    (texts : List String) (available : supported name) (notFunction : functions.find? (·.name == name) = none) :
    ExecutableExpression supported functions (call type name (texts.map word)) := by
  apply ExecutableExpression.external available notFunction
  intro argument member
  obtain ⟨text, _, rfl⟩ := List.mem_map.mp member
  exact .word _ _ _

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  rcases statementMember with rfl | rfl
  all_goals simp only [expression, ExecutableStatement]
  · apply ExecutableExpression.external (name := "mstore") (available _ (by simp [usedNames])) (by rfl)
    intro argument member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .word _ _ _
    · cases scenario <;> first
        | exact atoms _ .word "create" ["0", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create" ["1", "0", "0"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["0", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
        | exact atoms _ .word "create2" ["1", "0", "0", "7"] (available _ (by simp [usedNames])) (by rfl)
  · exact atoms _ .unit "return" ["0", "32"] (available _ (by simp [usedNames])) (by rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) (scenario : Scenario) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object (context scenario) [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for admitted CREATE and CREATE2
attempts that fault after the nonce advance: an absent target in an incomplete
world, a target with unknown code, and two endowment overflows. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel (context scenario) (result scenario)
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate (context scenario)) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection (InitCatalogCorrespondence.InitCatalogConnection.empty rfl (by decide)) (context scenario)
    (by cases scenario <;> rfl) (empty_links object scenario) (source object scenario)

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Creator"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"creation fault: compile failed: {reprStr error}")
  let prepared := object.instantiate (context scenario)
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"creation fault: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .languageFailure failure =>
        unless failure == .word (reason scenario) do
          throw (IO.userError s!"creation fault: wrong reason for {reprStr scenario}: {reprStr failure}")
    | outcome =>
        throw (IO.userError s!"creation fault: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.absent, .unknownCode, .overflow, .overflow2] do
    check scenario

end Tests.RustHullCreationFaultCorrespondence
end

section
-- leanmerge: from Solcore.Test.RustHullImageComparison
set_option autoImplicit false
namespace Tests.RustHullImageComparison
open Solcore Core Solcore.Frontend.RustHull
private def require (test : Bool) (label : String) : IO Unit :=
  unless test do throw (IO.userError label)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def program (bytes : List UInt8) (mapping : WordMapping.Entries) (size : Nat)
    (suffix : Bool := false) : Core.Program := {
  body := ImageComparison.compareBytes bytes (WordMapping.literal mapping) (.word (word size)) suffix
  resultType := LanguageResult.resultType .bool
  dataDefinitions := Memory.definitions
}
private def expect (label : String) (source : Core.Program) (expected : Bool) : IO Unit := do
  require source.check s!"{label}: ill typed"
  match source.run 3000000 with
  | .done actual => require (actual == .inRight .word (.bool expected)) s!"{label}: {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
def run : IO Unit := do
  let bytes := (List.range 97).map fun index => UInt8.ofNat (index + 3)
  let entries := Memory.packBytes bytes
  expect "exact image" (program bytes entries 97) true
  expect "entry order" (program bytes entries.reverse 97) true
  expect "length mismatch" (program bytes entries 98) false
  expect "argument suffix" (program bytes (Memory.packBytes (bytes ++ [99, 98])) 99 true) true
  expect "short prefix" (program bytes entries 96 true) false
  expect "missing nonzero word" (program bytes [] 97) false
  expect "missing zero words" (program (List.replicate 97 0) [] 97) true
  expect "empty image" (program [] entries 0) true
  expect "outside entries" (program bytes ((word 999, word 1) :: entries) 97) true
  let original := WordMapping.lookupEntries (word 0) entries
  expect "first duplicate wins" (program bytes ((word 0, original) :: (word 0, word 0) :: entries) 97) true
  expect "bad first duplicate" (program bytes ((word 0, word 0) :: entries) 97) false
  let zeros := Memory.packBytes (List.replicate 97 0)
  expect "nonzero extra input" (program (List.replicate 97 0) ((word 0, word 1) :: zeros) 97) false
  expect "ignored partial tail" (program [1] [(word 0, word (2 ^ 248 + 3))] 1) true
  let large := (List.range 24576).map fun index => UInt8.ofNat (index % 251 + 1)
  let big := program large (Memory.packBytes large) 24576
  expect "all deployed-code bitmap buckets" big true
  match big.runStateful 100 with
  | .outOfFuel state => require (runStateful 3000000 state == big.runStateful 3000100) "image comparison resume"
  | _ => throw (IO.userError "expected image comparison suspension")
end Tests.RustHullImageComparison
end

section
-- leanmerge: from Solcore.Test.RustHullLinkedContract
/-! Synthetic object-frame regressions for linking, constructor input and
storage transfer. Actual compiler image parity is exercised by the export gate. -/
set_option autoImplicit false
namespace Tests.RustHullLinkedContract
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {α : Type} (label : String) : LowerM α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def symbol (value : String) : YulExpr := ⟨.literal (.string ("\"" ++ value ++ "\"")), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def code (body : List YulStmt) : CodeBlock := {
  stmts := [⟨.assembly body, none⟩]
  functions := []
}
private def bytes (values : List Nat) : List UInt8 := values.map UInt8.ofNat
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def deployName := "ConstructorObjectNameLongerThanAnEvmWordBytes"
private def runtimeName := "RuntimeObjectNameLongerThanThirtyTwoBytes"
private def runtimeBytes : List UInt8 := bytes [0x60, 0, 0x55, 0xf3]
private def images : List CodeImage.Image := [
  {path := [deployName], bytes := bytes [0xaa, 0xbb] ++ runtimeBytes,
    embeds := [{name := runtimeName, offset := 2, size := runtimeBytes.length}]},
  {path := [deployName, runtimeName], bytes := runtimeBytes}]
private def runtimeBody : List YulStmt := [
  action "mstore" [w 0, call "sload" [w 0]],
  action "mstore" [w 32, call "sload" [w 1]],
  action "mstore" [w 64, call "codesize"], action "return" [w 0, w 96]]
private def source (init : List YulStmt) (runtime : List YulStmt := runtimeBody) : Program := {
  functions := []
  entryPoints := []
  objects := [.object deployName (code init) [.object runtimeName (code runtime) [] none] none]
}
private def initializer : List YulStmt := [
  action "sstore" [w 0, w 7],
  action "codecopy" [w 0, call "datasize" [symbol deployName],
    call "sub" [call "codesize", call "datasize" [symbol deployName]]],
  action "sstore" [w 0, call "mload" [w 0]],
  action "sstore" [w 1, call "calldatasize"],
  action "codecopy" [w 0, call "dataoffset" [symbol runtimeName], call "datasize" [symbol runtimeName]],
  action "return" [w 0, call "datasize" [symbol runtimeName]],
  action "sstore" [w 0, w 99]]

private def rejects (label : String) (value : LowerM Contract.Prepared) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"{label}: malformed linked object was accepted")

private def expectBytes (label : String) (outcome : Contract.Outcome) (expected : List UInt8) : IO Core.WordMapping.Entries :=
  match outcome with
  | .returned actual storage => do
      require (actual == expected) s!"{label}: unexpected output {reprStr actual}"
      pure storage
  | other => throw (IO.userError s!"{label}: {reprStr other}")

def runDeploymentContext : IO Unit := do
  let program := source [
    action "sstore" [w 0, call "calldatasize"],
    action "sstore" [w 1, call "callvalue"],
    action "sstore" [w 2, call "selfbalance"],
    action "sstore" [w 3, call "call" [w 0, call "address", w 0, w 0, w 0, w 0, w 0]],
    action "codecopy" [w 0, call "datasize" [symbol deployName], w 32],
    action "sstore" [w 4, call "mload" [w 0]],
    action "codecopy" [w 0, call "dataoffset" [symbol runtimeName], call "datasize" [symbol runtimeName]],
    action "return" [w 0, call "datasize" [symbol runtimeName]]]
  let prepared ← get "deployment context helper" (LinkedContract.prepareDeployment program [deployName]
    images (wordBytes 42) {
      calldata := bytes [0xaa, 0xbb]
      address := Core.Word.ofNatModulo 0xaaa
      value := Core.Word.ofNatModulo 17
      balance := Core.Word.ofNatModulo 117})
  require (prepared.context.calldata.isEmpty && !prepared.context.selfCodeAvailable)
    "deployment helper retained runtime-only frame context"
  let storage ← expectBytes "deployment helper preserves linked constructor arguments"
    (Contract.run prepared) runtimeBytes
  for (slot, value) in [(0, 0), (1, 17), (2, 117), (3, 1), (4, 42)] do
    require ((Core.WordMapping.lookupEntries (Core.Word.ofNatModulo slot) storage).val = value)
      s!"deployment helper lost constructor state at {slot}"

def runDatacopy : IO Unit := do
  let init := [
    action "datacopy" [w 0, call "datasize" [symbol deployName], w 32],
    action "sstore" [w 0, call "mload" [w 0]],
    action "datacopy" [w 5, call "dataoffset" [symbol runtimeName], call "datasize" [symbol runtimeName]],
    action "return" [w 5, call "datasize" [symbol runtimeName]]]
  let runtime := [
    action "mstore" [w 0, w (Core.wordModulus - 1)],
    action "datacopy" [w 3, call "add" [call "dataoffset" [symbol runtimeName], w 1], w 6],
    action "return" [w 0, w 10]]
  let program := source init runtime
  let constructor ← get "datacopy linked constructor"
    (LinkedContract.prepareDeployment program [deployName] images (wordBytes 42))
  let storage ← expectBytes "datacopy returns exact embedded runtime at unaligned destination"
    (Contract.run constructor) runtimeBytes
  require ((Core.WordMapping.lookupEntries Core.Word.zero storage).val = 42)
    "datacopy did not read appended constructor arguments"
  let runtime ← get "datacopy linked runtime"
    (LinkedContract.prepare program [deployName, runtimeName] images)
  let _ ← expectBytes "datacopy selects runtime image and zero pads beyond its end"
    (Contract.run runtime) (bytes [0xff, 0xff, 0xff, 0, 0x55, 0xf3, 0, 0, 0, 0xff])
  let overflow := source [] [
    action "mstore" [w 0, w (Core.wordModulus - 1)],
    action "mstore" [w 32, w (Core.wordModulus - 1)],
    action "datacopy" [w 31, w (Core.wordModulus - 1), w 2],
    action "return" [w 30, w 4]]
  let overflow ← get "datacopy source offset does not wrap"
    (LinkedContract.prepare overflow [deployName, runtimeName] images)
  let _ ← expectBytes "datacopy zero padding across a packed word boundary"
    (Contract.run overflow) (bytes [0xff, 0, 0, 0xff])
  let noImage := source [] [action "datacopy" [w 0, w 0, w 1], action "stop"]
  rejects "datacopy requires exact code image"
    (Contract.prepare noImage [deployName, runtimeName])
  pure ()

def runInitCodeLimit : IO Unit := do
  let program := source []
  let suffix := List.replicate (49152 - 6) (0 : UInt8)
  let prepared ← get "init code size exact boundary including arguments"
    (LinkedContract.prepareDeployment program [deployName] images suffix)
  require prepared.context.deploying "size boundary did not prepare a deployment"
  rejects "init code one byte over boundary including arguments"
    (LinkedContract.prepareDeployment program [deployName] images (0 :: suffix))
  let oversized := images.map fun image => if image.path == [deployName] then
    {image with bytes := image.bytes ++ List.replicate (49153 - 6) 0} else image
  rejects "init code image itself exceeds boundary"
    (LinkedContract.prepareDeployment program [deployName] oversized)

def run : IO Unit := do
  runDeploymentContext
  runDatacopy
  runInitCodeLimit
  let program := source initializer
  let constructor ← get "constructor" (LinkedContract.prepare program [deployName] images (wordBytes 42))
  let state ← expectBytes "constructor returns exact embedded bytes" (Contract.run constructor) runtimeBytes
  require ((Core.WordMapping.lookupEntries Core.Word.zero state).val = 42)
    "constructor tail arguments were not loaded into storage"
  require ((Core.WordMapping.lookupEntries (Core.Word.ofNatModulo 1) state).val = 0)
    "constructor arguments leaked into calldata"
  let runtime ← get "runtime compilation" (LinkedContract.compileObject program [deployName, runtimeName] images)
  let _ ← expectBytes "runtime retains constructor storage"
    (Contract.run (runtime.instantiate {storage := state, calldata := bytes [1, 2, 3]}))
    (wordBytes 42 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  let initialStorage := [(Core.Word.zero, Core.Word.ofNatModulo 5)]
  let revertedSource := source [action "sstore" [w 0, w 99], action "mstore8" [w 0, w 0xde],
    action "revert" [w 0, w 1], action "sstore" [w 0, w 77]]
  let reverted ← get "reverting constructor" (LinkedContract.prepare revertedSource [deployName] images []
    {storage := initialStorage})
  match Contract.run reverted with
  | .reverted actual => require (actual == bytes [0xde]) "wrong constructor revert payload"
  | other => throw (IO.userError s!"constructor did not revert: {reprStr other}")
  let _ ← expectBytes "reverting constructor does not publish storage"
    (Contract.run (runtime.instantiate reverted.context))
    (wordBytes 5 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  match Contract.run constructor 100 with
  | .outOfFuel machine =>
      let resumed ← expectBytes "linked constructor resume" (Contract.resume machine) runtimeBytes
      require ((Core.WordMapping.lookupEntries Core.Word.zero resumed).val = 42)
        "resumed constructor lost storage writes"
  | other => throw (IO.userError s!"constructor should suspend: {reprStr other}")
  let badInit := source [action "pop" [call "datasize" [symbol "UnknownObject"]]]
  rejects "unknown linked symbol" (LinkedContract.prepare badInit [deployName] images)
  let childOnly ← get "unselected object's symbols stay independent"
    (LinkedContract.prepare badInit [deployName, runtimeName] images)
  let _ ← expectBytes "runtime skips unrelated invalid constructor symbols" (Contract.run childOnly)
    (wordBytes 0 ++ wordBytes 0 ++ wordBytes runtimeBytes.length)
  rejects "missing linked image" (LinkedContract.prepare program [deployName] images.tail)
  let badImages := images.map fun image => if image.path == [deployName] then
    {image with bytes := bytes [0xaa, 0xbb, 0, 0, 0, 0]} else image
  rejects "mismatched embedded bytes" (LinkedContract.prepare program [deployName] badImages)
  let shadowed := source [] [
    action "mstore" [w 0, call "datasize" [w 41]], action "return" [w 0, w 32],
    ⟨.functionDef (name "datasize") [name "x"] [name "r"] [
      ⟨.assign [name "r"] (call "add" [⟨.ident (name "x"), none⟩, w 1]), none⟩], none⟩]
  let shadowed ← get "hoisted local datasize shadow"
    (LinkedContract.prepare shadowed [deployName, runtimeName] images)
  let _ ← expectBytes "local symbol intrinsic shadowing" (Contract.run shadowed) (wordBytes 42)
  let selfOffset := source [] [action "mstore" [w 0, call "dataoffset" [symbol runtimeName]],
    action "return" [w 0, w 32]]
  let selfOffset ← get "current image offset"
    (LinkedContract.prepare selfOffset [deployName, runtimeName] images)
  let _ ← expectBytes "current object starts at zero" (Contract.run selfOffset) (wordBytes 0)
  pure ()

end Tests.RustHullLinkedContract
end

section
-- leanmerge: from Solcore.Test.RustHullObjectLinking
set_option autoImplicit false
namespace Tests.RustHullObjectLinking
open Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def call (name symbol : String) : YulExpr :=
  ⟨.call ⟨name, none⟩ [⟨.literal (.string (Lean.toJson symbol).compress), none⟩], none⟩

private def program (body : List YulStmt) : Program :=
  ⟨[], [], [.object "Deploy" ⟨[⟨.assembly body, none⟩], [], none⟩
    [.object "Runtime" ⟨[], [], none⟩ [] none] none], none⟩

private def image : CodeImage.Image :=
  {path := ["Deploy"], bytes := [1, 2, 3, 4, 5], embeds := [⟨⟨3, 2⟩, "Runtime"⟩]}

private def linked (input : Program) (image : CodeImage.Image := image) : IO Program :=
  match ObjectLinking.link input image with
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

private def bodyOf (input : Program) : List YulStmt :=
  match input.objects with
  | [.object _ ⟨[⟨.assembly body, _⟩], _, _⟩ _ _] => body
  | _ => []

def run : IO Unit := do
  let input := program [⟨.expression (call "datasize" "Deploy"), none⟩,
    ⟨.expression (call "datasize" "Runtime"), none⟩,
    ⟨.expression (call "dataoffset" "Runtime"), none⟩]
  let output ← linked input
  let expected := [5, 2, 3].map fun value =>
    YulStmt.mk (.expression ⟨.literal (.number (toString value)), none⟩) none
  require (bodyOf output == expected) "object symbol extents were not resolved exactly"

  let unknown := program [⟨.expression (call "datasize" "Absent"), none⟩]
  require (ObjectLinking.link unknown image).toOption.isNone "unknown object symbol was accepted"
  let dynamic := program [⟨.expression ⟨.call ⟨"dataoffset", none⟩ [⟨.ident ⟨"x", none⟩, none⟩], none⟩, none⟩]
  require (ObjectLinking.link dynamic image).toOption.isNone "dynamic object symbol was accepted"

  let long := "ThisRuntimeObjectNameExceedsThirtyTwoBytes"
  let longImage := {image with embeds := [⟨⟨3, 2⟩, long⟩]}
  let longInput := program [⟨.expression (call "dataoffset" long), none⟩]
  require (bodyOf (← linked longInput longImage) ==
    [⟨.expression ⟨.literal (.number "3"), none⟩, none⟩])
    "object symbol was treated as a word-sized string literal"

  let shadow : YulStmt := ⟨.functionDef ⟨"datasize", none⟩ [] [⟨"r", none⟩] [], none⟩
  let shadowed := program [⟨.expression (call "datasize" "Absent"), none⟩, shadow]
  require ((← linked shadowed) == shadowed) "hoisted Yul function did not shadow intrinsic name"
  let innerShadow := program [⟨.block [shadow], none⟩, ⟨.expression (call "datasize" "Runtime"), none⟩]
  require (bodyOf (← linked innerShadow) ==
    [⟨.block [shadow], none⟩, ⟨.expression ⟨.literal (.number "2"), none⟩, none⟩])
    "block-local intrinsic shadow escaped its scope"

  let nested : Program := {input with objects := [.object "Deploy" ⟨[], [], none⟩
    [.object "Runtime" ⟨[⟨.assembly [⟨.expression (call "datasize" "Deploy"), none⟩], none⟩], [], none⟩ [] none] none]}
  require ((← linked nested) == nested) "parent image rewrote a child's symbol namespace"

end Tests.RustHullObjectLinking
end
