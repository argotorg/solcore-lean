import Solcore.Frontend.RustHull.ContractCallModeExecutionCorrespondence
import Solcore.Frontend.RustHull.ContractCallModeSupported

/-! Inline Yul `if`, nested blocks and `switch` reach the actual Yul lowering
through the call-mode public theorem. In the branching scenario an `if` on a
zero local skips its `return`, a nested block reads memory into a local of its
own and stores it under an `if`, and a last `if` returns the stored word 7
before a statement that is not reached. In the switching scenario a `switch` on
`mload(0)` skips the first case, runs the second with a local of its own, and a
second `switch` returns the word 20 from its default body. The independent
source follows `YulSemantics`. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.RustHullYulControlCorrespondence
open Solcore Solcore.Frontend.RustHull Correspondence DerivationCorrespondence

inductive Scenario where
  | branching | switching
  deriving DecidableEq, Repr

private abbrev w := Core.Word.ofNatModulo
private def number (text : String) : YulExpr := ⟨.literal (.number text), none⟩
private def reading (text : String) : YulExpr := ⟨.ident ⟨text, none⟩, none⟩
private def builtin (text : String) (arguments : List YulExpr) : YulExpr := ⟨.call ⟨text, none⟩ arguments, none⟩
private def perform (expression : YulExpr) : YulStmt := ⟨.expression expression, none⟩
private def declare (text : String) (value : YulExpr) : YulStmt := ⟨.letDecl [⟨text, none⟩] (some value), none⟩
private def nested (body : List YulStmt) : YulStmt := ⟨.block body, none⟩
private def when (condition : YulExpr) (body : List YulStmt) : YulStmt := ⟨.ifThen condition body, none⟩
private def choose (value : YulExpr) (cases : List (String × List YulStmt)) (defaultBody : List YulStmt) : YulStmt :=
  ⟨.switch value (cases.map fun (text, body) => ⟨.number text, body, none⟩) (some defaultBody), none⟩

/-- `let c := 0 if c { return(0, 32) } mstore(0, 7) { let inner := mload(0)
if 1 { mstore(32, inner) } } if 1 { return(32, 32) } mstore(32, 9)` -/
def branchingBlock : List YulStmt :=
  [declare "c" (number "0"),
   when (reading "c") [perform (builtin "return" [number "0", number "32"])],
   perform (builtin "mstore" [number "0", number "7"]),
   nested [declare "inner" (builtin "mload" [number "0"]),
     when (number "1") [perform (builtin "mstore" [number "32", reading "inner"])]],
   when (number "1") [perform (builtin "return" [number "32", number "32"])],
   perform (builtin "mstore" [number "32", number "9"])]

def switchCases : List (String × List YulStmt) :=
  [("1", [perform (builtin "mstore" [number "32", number "10"])]),
   ("2", [declare "v" (number "20"), perform (builtin "mstore" [number "32", reading "v"])])]

def exitCases : List (String × List YulStmt) := [("1", [perform (builtin "return" [number "0", number "32"])])]

/-- `mstore(0, 2) switch mload(0) case 1 { mstore(32, 10) } case 2 { let v := 20
mstore(32, v) } default { mstore(32, 30) } switch 5 case 1 { return(0, 32) }
default { return(32, 32) }` -/
def switchingBlock : List YulStmt :=
  [perform (builtin "mstore" [number "0", number "2"]),
   choose (builtin "mload" [number "0"]) switchCases [perform (builtin "mstore" [number "32", number "30"])],
   choose (number "5") exitCases [perform (builtin "return" [number "32", number "32"])]]

def body : Scenario → List YulStmt
  | .branching => branchingBlock
  | .switching => switchingBlock

def rootBytes : List UInt8 := [0]
def code (scenario : Scenario) : CodeBlock := {stmts := [⟨.assembly (body scenario), none⟩], functions := []}
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
def returned (offset length : Core.Word) (state : SourceState) : SourceState :=
  YulSemantics.withFrame state (TerminationSemantics.terminate (YulSemantics.frame state) 1 offset length).2
def allocated (value : Core.Word) (state : SourceState) : SourceState := (Semantics.allocate state (.word value)).2

/-- The nested block's local holds the word that `mstore(0, 7)` wrote. -/
def branchingWritten (object : Contract.CompiledObject) : SourceState :=
  stored (w 0) (w 7) (allocated (w 0) (initial object))
def branchingFinal (object : Contract.CompiledObject) : SourceState :=
  let inner := loaded (w 0) (branchingWritten object)
  returned (w 32) (w 32) (stored (w 32) inner (allocated inner (touched (w 0) (branchingWritten object))))
/-- The second case runs with the word that `mstore(0, 2)` wrote as scrutinee. -/
def switchingWritten (object : Contract.CompiledObject) : SourceState := stored (w 0) (w 2) (initial object)
def switchingFinal (object : Contract.CompiledObject) : SourceState :=
  returned (w 32) (w 32) (stored (w 32) (w 20) (allocated (w 20) (touched (w 0) (switchingWritten object))))
def finalState (object : Contract.CompiledObject) : Scenario → SourceState
  | .branching => branchingFinal object
  | .switching => switchingFinal object
def result : Semantics.Result Semantics.Value := .fault (.language Core.Word.maximum)
def halted : Semantics.Control := .fault (.language Core.Word.maximum)

private theorem branching_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] branchingBlock (initial object) halted (branchingFinal object) :=
  YulSemantics.Run.letValue (.literal (word := w 0) (by decide +kernel))
  (YulSemantics.Run.compound (YulSemantics.Compound.ifFalse (YulSemantics.Eval.ident rfl rfl))
  (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 7, w 0])
    (.cons (.literal (word := w 7) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.compound (YulSemantics.Compound.block
    (YulSemantics.Run.letValue (YulSemantics.Eval.call (words := [w 0])
      (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
    (YulSemantics.Run.compound (YulSemantics.Compound.ifTrue (.literal (word := w 1) (by decide +kernel))
        (by decide)
      (YulSemantics.Run.expression (YulSemantics.Eval.call
        (words := [loaded (w 0) (branchingWritten object), w 32])
        (.cons (YulSemantics.Eval.ident (word := loaded (w 0) (branchingWritten object)) rfl rfl)
          (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
      YulSemantics.Run.nil))
    YulSemantics.Run.nil)))
  (YulSemantics.Run.compoundStop (YulSemantics.Compound.ifTrue (.literal (word := w 1) (by decide +kernel))
      (by decide)
    (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
      .returned)))
    (by intro impossible; cases impossible)))))

private theorem second_selected (object : Contract.CompiledObject) :
    YulSemantics.select (loaded (w 0) (switchingWritten object))
      (switchCases.map fun (text, body) => ⟨.number text, body, none⟩) =
      some [declare "v" (number "20"), perform (builtin "mstore" [number "32", reading "v"])] := by
  have first : YulSemantics.literalWord? (.number "1") ≠ some (loaded (w 0) (switchingWritten object)) := by
    rw [show loaded (w 0) (switchingWritten object) = w 2 from rfl]
    decide +kernel
  have second : YulSemantics.literalWord? (.number "2") = some (loaded (w 0) (switchingWritten object)) := by
    rw [show loaded (w 0) (switchingWritten object) = w 2 from rfl]
    decide +kernel
  simp only [switchCases, List.map_cons, List.map_nil, YulSemantics.select, if_neg first, if_pos second]

private theorem exit_unselected :
    YulSemantics.select (w 5) (exitCases.map fun (text, body) => ⟨.number text, body, none⟩) = none := by
  have first : YulSemantics.literalWord? (.number "1") ≠ some (w 5) := by decide +kernel
  simp only [exitCases, List.map_cons, List.map_nil, YulSemantics.select, if_neg first]

private theorem switching_run (object : Contract.CompiledObject) :
    YulSemantics.Run [] switchingBlock (initial object) halted (switchingFinal object) :=
  YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 2, w 0])
    (.cons (.literal (word := w 2) (by decide +kernel)) (.cons (.literal (word := w 0) (by decide +kernel)) .nil))
    .mstore)
  (YulSemantics.Run.compound (YulSemantics.Compound.switchCase (YulSemantics.Eval.call (words := [w 0])
      (.cons (.literal (word := w 0) (by decide +kernel)) .nil) .mload)
    (second_selected object)
    (YulSemantics.Run.letValue (.literal (word := w 20) (by decide +kernel))
    (YulSemantics.Run.expression (YulSemantics.Eval.call (words := [w 20, w 32])
      (.cons (YulSemantics.Eval.ident (word := w 20) rfl rfl)
        (.cons (.literal (word := w 32) (by decide +kernel)) .nil)) .mstore)
    YulSemantics.Run.nil)))
  (YulSemantics.Run.compoundStop (YulSemantics.Compound.switchDefault (.literal (word := w 5) (by decide +kernel))
      exit_unselected
    (YulSemantics.Run.expressionFault (YulSemantics.Eval.call (words := [w 32, w 32])
      (.cons (.literal (word := w 32) (by decide +kernel)) (.cons (.literal (word := w 32) (by decide +kernel)) .nil))
      .returned)))
    (by intro impossible; cases impossible)))

theorem source (object : Contract.CompiledObject) (scenario : Scenario) :
    Semantics.EvalFunction (functions scenario) effects (AccountRuntime.frameFunction (code scenario)) []
      (initial object) result (finalState object scenario) := by
  apply Semantics.EvalFunction.body (control := .fault _) rfl
  cases scenario
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (branching_run object))
      (by intro impossible; cases impossible)
  · exact .stop (by intros; intro impossible; cases impossible) (.assembly rfl (switching_run object))
      (by intro impossible; cases impossible)

def usedNames : List String := ["mstore", "mload", "return"]

private theorem block_eligible {supported : String → Prop} (available : ∀ name ∈ usedNames, supported name)
    (scenario : Scenario) : YulFragment.Eligible supported (body scenario) := by
  refine ⟨⟨"mstore", available "mstore" (by simp [usedNames])⟩, ?_⟩
  cases scenario
  all_goals
    simp only [body, branchingBlock, switchingBlock, switchCases, exitCases, declare, perform, nested, when, choose,
      builtin, reading, number, List.map_cons, List.map_nil]
    repeat' (first
      | exact available _ (by simp [usedNames])
      | constructor
      | simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true, Option.getD_some,
          ne_eq, reduceCtorEq, not_false_eq_true])

theorem eligible (scenario : Scenario) {supported : String → Prop}
    (available : ∀ name ∈ usedNames, supported name) :
    ExecutableProgram supported (functions scenario) := by
  intro function member statement statementMember
  simp only [functions, List.mem_cons, List.not_mem_nil, or_false] at member
  subst function
  simp only [AccountRuntime.frameFunction, code, List.mem_cons, List.not_mem_nil, or_false] at statementMember
  subst statementMember
  simp only [ExecutableStatement]
  exact block_eligible available scenario

private theorem names_supported : ∀ name ∈ usedNames, ContractCallModeCorrespondence.supported true name := by
  intro name member
  simp only [usedNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.store, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl (.inl ⟨.load, rfl⟩)))))))))
  · exact .inl (.inl (.inl (.inl (.inl (.inl (.inr ⟨.returned, rfl⟩))))))

private theorem empty_connection : ModeChildCatalogExecutionCorrespondence.CatalogConnection [] [] [] := by
  intro address source selected
  simp [ChildFrameSemantics.select] at selected

private theorem empty_links (object : Contract.CompiledObject) :
    ContractCallModeCorrespondence.InitialContextLinks (some rootBytes) [] object context [] := by
  intro anchor member
  simp at member

/-- Public consumer of the call-mode theorem for inline Yul `if`, nested blocks
and `switch`, including control that stops the statement list from a nested
body. -/
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
  | .branching => List.replicate 31 0 ++ [7]
  | .switching => List.replicate 31 0 ++ [20]

private def check (scenario : Scenario) : IO Unit := do
  let object ← match Contract.compileObject (program scenario) ["Assembler"] 64 (some rootBytes) [] with
    | .ok object => pure object
    | .error error => throw (IO.userError s!"Yul control correspondence: compile failed: {reprStr error}")
  let prepared := object.instantiate context
  let checkpoint ← match (Contract.runWithReceipt prepared 0).outcome with
    | .outOfFuel checkpoint => pure checkpoint
    | outcome => throw (IO.userError s!"Yul control correspondence: zero fuel completed: {reprStr outcome}")
  for receipt in [Contract.runWithReceipt prepared 1000000, Contract.resumeWithReceipt checkpoint 1000000] do
    match receipt.outcome with
    | .returned bytes _ =>
        unless bytes == expected scenario do
          throw (IO.userError s!"Yul control correspondence: wrong bytes for {reprStr scenario}: {reprStr bytes}")
    | outcome =>
        throw (IO.userError s!"Yul control correspondence: unexpected outcome for {reprStr scenario}: {reprStr outcome}")

def run : IO Unit := do
  for scenario in [Scenario.branching, .switching] do
    check scenario

end Tests.RustHullYulControlCorrespondence
