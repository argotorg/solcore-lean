import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! Inline Yul blocks of several statements reach the actual Yul lowering
through the call-mode public theorem: `let` with and without a value, an
assignment, variables, nested builtin calls, and a Hull local the block assigns
and reads. In the ordered scenario the second `mstore` evaluates `msize()`
before `mload(32)` expands memory, so the block returns the word 32; the
opposite argument order would return 64. In the Hull-local scenario the block
assigns 42 to the Hull local `x`, stores it and returns it. The independent
source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullYulBlockCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | ordered | hullLocal
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def reading (text : String) : YulExpr := ⟨.ident ⟨text, none⟩, none⟩
private def builtin (text : String) (arguments : List YulExpr) : YulExpr := ⟨.call ⟨text, none⟩ arguments, none⟩
private def perform (expression : YulExpr) : YulStmt := ⟨.expression expression, none⟩
private def declare (text : String) (value : Option YulExpr) : YulStmt := ⟨.letDecl [⟨text, none⟩] value, none⟩
private def assign (text : String) (value : YulExpr) : YulStmt := ⟨.assign [⟨text, none⟩] value, none⟩

/-- `mstore(0, 7) mstore(mload(32), msize()) let r := mload(0) let z z := r
mstore(32, z) return(32, 32)` -/
def orderedBlock : List YulStmt :=
  [perform (builtin "mstore" [number "0", number "7"]),
   perform (builtin "mstore" [builtin "mload" [number "32"], builtin "msize" []]),
   declare "r" (some (builtin "mload" [number "0"])),
   declare "z" none,
   assign "z" (reading "r"),
   perform (builtin "mstore" [number "32", reading "z"]),
   perform (builtin "return" [number "32", number "32"])]

/-- `x := 42 mstore(0, x) return(0, 32)`, after the Hull declaration `let x : word`. -/
def localBlock : List YulStmt :=
  [assign "x" (number "42"),
   perform (builtin "mstore" [number "0", reading "x"]),
   perform (builtin "return" [number "0", number "32"])]

def rootBytes : List UInt8 := [0]
def statements : Scenario → List Stmt
  | .ordered => [⟨.assembly orderedBlock, none⟩]
  | .hullLocal => [⟨.letDecl "x" .word, none⟩, ⟨.assembly localBlock, none⟩]
def code (scenario : Scenario) : CodeBlock := {stmts := statements scenario, functions := []}
def program (scenario : Scenario) : Program :=
  {entryPoints := [], functions := [], objects := [.object "Assembler" (code scenario) []]}
def functions (scenario : Scenario) : List Function := [AccountRuntime.frameFunction (code scenario)]
def effects : Semantics.ExternalSemantics RuntimeCallModeSemantics.State :=
  ChildFrameModeSemantics.effectsAt [] 1 (some rootBytes)
def context : Contract.Context := {}

abbrev SourceState := Semantics.State RuntimeCallModeSemantics.State
def initial (object : Contract.CompiledObject) : SourceState :=
  ⟨[], ContractCallCorrespondence.contextInitialState (some rootBytes) object (Contract.normalizeContext context)⟩

/-- The independent effects of the fragment's statements. -/
def stored (offset value : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mstore (YulSemantics.frame state).memory offset value).2}
def touched (offset : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state {YulSemantics.frame state with
    memory := (MemorySemantics.mload (YulSemantics.frame state).memory offset).2}
def loaded (offset : Core.Word) (state : SourceState) : Core.Word :=
  MemorySemantics.readWord (YulSemantics.frame state).memory.words offset
def size (state : SourceState) : Core.Word := (YulSemantics.frame state).memory.size
def returned (offset length : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state (TerminationSemantics.terminate (YulSemantics.frame state) 1 offset length).2
def allocated (value : Core.Word) (state : SourceState) : SourceState := (Semantics.allocate state (.word value)).2
def assigned (location : Nat) (value : Core.Word) (state : SourceState) : SourceState :=
  {state with heap := state.heap.set location (.word value)}

/-- `mstore(mload(32), msize())` takes the size before `mload(32)` expands memory. -/
def orderedFirst (object : Contract.CompiledObject) : SourceState := stored (w 0) (w 7) (initial object)
def orderedSecond (object : Contract.CompiledObject) : SourceState :=
  stored (loaded (w 32) (orderedFirst object)) (size (orderedFirst object)) (touched (w 32) (orderedFirst object))
def orderedValue (object : Contract.CompiledObject) : Core.Word := loaded (w 0) (orderedSecond object)
def orderedLocals (object : Contract.CompiledObject) : SourceState :=
  allocated Core.Word.zero (allocated (orderedValue object) (touched (w 0) (orderedSecond object)))
def orderedFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 32) (w 32) (stored (w 32) (orderedValue object) (assigned 1 (orderedValue object) (orderedLocals object)))
def localFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 0) (w 32) (stored (w 0) (w 42) (assigned 0 (w 42) (allocated Core.Word.zero (initial object))))
def finalState (object : Contract.CompiledObject) : Scenario → SourceState
  | .ordered => orderedFinal object
  | .hullLocal => localFinal object
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def halted : Semantics.Control := .fault (.language Core.Word.maximum)

private theorem ordered_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] orderedBlock (initial object) halted (orderedFinal object) :=
  YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 7, w 0])
    (.cons (.literal (word := w 7) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.expression (YulSemantics.Eval.call
    (words := [size (orderedFirst object), loaded (w 32) (orderedFirst object)])
    (.cons (YulSemantics.Eval.call (words := []) .nil .msize)
      (.cons (YulSemantics.Eval.call (words := [w 32])
        (.cons (.literal (word := w 32) (by decide +kernel)) .nil) .mload) .nil))
    .mstore)
  (YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 0])
    (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
  (YulSemantics.Run.letZero
  (YulSemantics.Run.assign (YulSemantics.Eval.ident (word := orderedValue object) rfl rfl) rfl
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [orderedValue object, w 32])
    (.cons (YulSemantics.Eval.ident (word := orderedValue object) rfl rfl)
      (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
  (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
    (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
    .returned)))))))

private theorem local_run (object : Contract.CompiledObject) :
    YulSemantics.Run [("x", 0)] localBlock (allocated Core.Word.zero (initial object)) halted (localFinal object) :=
  YulSemantics.Run.assign (.literal (word := w 42) (by decide +kernel)) rfl
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 42, w 0])
    (.cons (YulSemantics.Eval.ident (word := w 42) rfl rfl) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 0])
    (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .returned)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (ordered_run object))
      (by intro impossible; cases impossible)
  · exact .declare rfl rfl (.stop (by intros; intro impossible; cases impossible) (.assembly rfl (local_run object))
      (by intro impossible; cases impossible))

def usedNames : List String := ["mstore", "mload", "msize", "return"]

private theorem block_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name)
    {body : List YulStmt} (known : body = orderedBlock ∨ body = localBlock) : YulFragment.Eligible supported body := by
  refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
  intro statement member
  rcases known with rfl | rfl
  · simp only [orderedBlock, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      repeat' constructor
      all_goals exact available _ (by simp [usedNames])
  · simp only [localBlock, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals
      repeat' constructor
      all_goals exact available _ (by simp [usedNames])

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  cases scenario
  · simp only [AccountRuntime.frameFunction, code, statements, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    subst statementMember
    simp only [ExecutableStatement]
    exact block_eligible available (.inl rfl)
  · simp only [AccountRuntime.frameFunction, code, statements, List.mem_cons, List.not_mem_nil, or_false] at statementMember
    rcases statementMember with rfl | rfl
    · simp only [ExecutableStatement]
    · simp only [ExecutableStatement]
      exact block_eligible available (.inr rfl)

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.load, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.size, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul blocks of several
statements: Yul locals, an assignment, nested calls in Yul's right-to-left
argument order and a Hull local assigned and read by the block. -/
theorem public_resumes (scenario : Scenario) {object : Contract.CompiledObject}
    (accepted : Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] = .ok object) :
    ∃ value, ContractCallModeCorrespondence.PublicMessageRel context result
        (finalState object scenario).external value ∧
      ∃ required, ∀ initialFuel additional limit last,
        Contract.ReceiptResumes limit (Contract.runWithReceipt (object.instantiate context) initialFuel limit)
          additional last →
        (last = Contract.finish limit value ↔ required ≤ initialFuel + additional) ∧
        ((∃ checkpoint, last.outcome = .outOfFuel checkpoint) ↔ initialFuel + additional < required) := by
  exact ContractCallModeCorrespondence.compileObject_resumes_exact (height := 0) (code := code scenario) (by rfl)
    accepted rfl (eligible scenario names_supported) empty_connection context rfl (empty_links object)
    (source object scenario)

private def expected : Scenario → List UInt8
  | .ordered => List.replicate 31 0 ++ [32]
  | .hullLocal => List.replicate 31 0 ++ [42]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"Yul block correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"Yul block correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"Yul block correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"Yul block correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.ordered, .hullLocal] do
    check scenario

end Tests.RustHullYulBlockCorrespondence
