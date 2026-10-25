import Solcore.Frontend.RustHull.ContractCodeExecutionCorrespondence
import Solcore.Frontend.RustHull.RuntimeCodeEffectsSemantics

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
